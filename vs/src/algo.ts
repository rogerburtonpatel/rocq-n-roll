import { DeautoCoqtop, goal } from "./coqtop";
import {
  No,
  Result,
  Script,
  Sentence,
  TVar,
  Tactic,
  Yes,
  atomic,
  pure,
  subst,
} from "./syntax";
import {
  Tree,
  applyAllTree,
  applyEachTree,
  leafGoals,
  extractScriptTree,
  lengthTree,
  applyNthTree,
} from "./tree";

class Deauto {
  coqtop: DeautoCoqtop;
  fuel: number;
  env: Map<string, Tactic>;

  constructor(coqtop: DeautoCoqtop, env: Map<string, Tactic>) {
    this.coqtop = coqtop;
    this.fuel = 30; // can later expose way for user to override this
    this.env = env;
  }

  async treeifyAtomic(a: atomic, g: goal): Promise<Result<Tree>> {
    const out = await this.coqtop.runAtomic(a, g);
    if (Array.isArray(out)) {
      // atomic execution succeeded, out = gs
      return pure({
        type: "node",
        goal: g,
        atomic: a,
        children: out.map((g) => ({ type: "hole", goal: g })),
      });
    } else {
      // atomic execution failed, out = bot_n
      return new Yes(
        {
          type: "failed",
          goal: g,
          error: { type: "atomic_failure", atomic: a, level: out },
        },
        out
      );
    }
  }

  async treeifyTactic(t: Tactic, g: goal): Promise<Result<Tree>> {
    if (this.fuel === 0) {
      return new Yes(
        { type: "failed", goal: g, error: { type: "out_of_fuel" } },
        0
      );
    }

    var mr;
    switch (t.type) {
      case "empty":
        return pure({ type: "hole", goal: g });
      case "opaque":
        if (this.env.has(t.atomic)) {
          // preliminary support for looking up transparent custom tactics
          return this.treeifyTactic(this.env.get(t.atomic)!, g);
        } else {
          return this.treeifyAtomic(t.atomic, g);
        }
      case "semicolon":
        mr = await this.treeifyTactic(t.left, g);
        return mr.bindA((r) =>
          applyAllTree((g) => this.treeifyTactic(t.right, g), r)
        );
      case "dispatch":
        mr = await this.treeifyTactic(t.left, g);
        if (mr instanceof No) {
          return mr;
        }
        mr = mr as Yes<Tree>;
        if (lengthTree(mr.t) === t.right.length) {
          return mr.bindA((r) =>
            applyEachTree(
              t.right.map((t_) => (g) => this.treeifyTactic(t_, g)),
              r
            )
          );
        } else {
          if (mr.level === null) {
            return pure({
              type: "failed",
              goal: g,
              error: { type: "tactic_failure", tactic: t },
            });
          } else {
            return mr;
          }
        }
      case "first":
        const trace = (await this.deautoTacticFirsts(t.body, g)).reverse();
        if (trace.length === 0) {
          return pure({
            type: "failed",
            goal: g,
            error: { type: "tactic_failure", tactic: t },
          });
        } else {
          const head = trace[0];
          const tail = trace.slice(1).map((mr) => (mr as Yes<Tree>).t);
          if (head instanceof Yes) {
            return new Yes(
              { type: "trace", head: head.t, trace: tail },
              head.decr()
            );
          } else {
            return head;
          }
        }
      case "progress":
        mr = await this.treeifyTactic(t.body, g);
        if (mr instanceof No) {
          return mr;
        }
        mr = mr as Yes<Tree>;
        if (mr.level !== null) {
          return mr;
        }
        const gs = leafGoals(mr.t);
        if (gs.length === 1 && gs[0][1] === g[1]) {
          return new Yes(
            {
              type: "failed",
              goal: g,
              error: { type: "tactic_failure", tactic: t },
            },
            0
          );
        } else {
          return mr;
        }
      case "fix":
        this.fuel--;
        return this.treeifyTactic(subst(t.binder, t.body, t), g);
      case "tvar":
        return new No(0);
      // derived tacticals:
      case "try":
        return this.treeifyTactic(
          {
            type: "first",
            body: [t.body, { type: "empty" }],
          },
          g
        );
      case "repeat":
        const T: TVar = { type: "tvar", var: "T" };
        return this.treeifyTactic(
          {
            type: "fix",
            binder: T,
            body: {
              type: "try",
              body: {
                type: "semicolon",
                left: { type: "progress", body: t.body },
                right: T,
              },
            },
          },
          g
        );
      case "auto":
      case "eauto":
        const info = await this.scratch((_) => true, this.coqtop.writeAuto(t.type, g));
        return this.deautoScript(info, { type: "hole", goal: g });
      case "match":
        const first = await this.coqtop.generateMatches(t, g);
        return this.treeifyTactic(first, g);
    }
  }

  async deautoTacticFirsts(ts: Tactic[], g: goal): Promise<Result<Tree>[]> {
    if (ts.length === 0) {
      return [];
    }

    const head = ts[0];
    const tail = ts.slice(1);
    const mr = await this.scratch(
      (mr) => mr.failed(),
      this.treeifyTactic(head, g)
    );
    if (mr instanceof Yes && mr.level === 0) {
      return [mr, ...(await this.deautoTacticFirsts(tail, g))];
    } else {
      return [mr];
    }
  }

  async deautoSentence(s: Sentence, r: Tree): Promise<Result<Tree>> {
    switch (s.type) {
      case "one":
        return applyNthTree((g) => this.treeifyTactic(s.body, g), 1, r);
      case "nth":
        return applyNthTree((g) => this.treeifyTactic(s.body, g), s.n, r);
      case "all":
        return applyAllTree((g) => this.treeifyTactic(s.body, g), r);
    }
  }

  async deautoScript(p: Script, r: Tree): Promise<Result<Tree>> {
    if (p.length === 0) {
      return pure(r);
    }
    const head = p[0];
    const tail = p.slice(1);
    switch (head.type) {
      case "focus":
        if (lengthTree(r) >= 1) {
          return (
            await applyNthTree(
              async (g) =>
                (
                  await this.deautoScript(head.block, { type: "hole", goal: g })
                ).bind((r) =>
                  // check that goals solved before unfocusing
                  leafGoals(r).length > 0 ? new No<Tree>(0) : pure(r)
                ),
              1,
              r
            )
          ).bindA((r) => this.deautoScript(tail, r));
        } else {
          return new No<Tree>(0);
        }
      case "comment":
        return this.deautoScript(tail, r);
      default:
        return (await this.deautoSentence(head, r)).bindA((r) =>
          this.deautoScript(tail, r)
        );
    }
  }

  async scratch<T>(f: (t: T) => boolean, pt: Promise<T>) {
    this.coqtop.mark();
    const t = await pt;
    if (f(t)) {
      await this.coqtop.undo();
    }
    return t;
  }
}

export async function deautomate(
  path: string,
  prelude: string,
  env: Map<string, Tactic>,
  script: Script
): Promise<Script> {
  const coqtop = new DeautoCoqtop(path, prelude);
  const goal = await coqtop.init();

  const mr = await new Deauto(coqtop, env).deautoScript(script, {
    type: "hole",
    goal: goal,
  });
  if (mr instanceof No) {
    return [{ type: "comment", body: "deautomation failed unrecoverably" }];
  }

  return extractScriptTree((mr as Yes<Tree>).t);
}
