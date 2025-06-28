import { goal } from "./coqtop";
import { unscript, untactic } from "./print";
import {
  Comment,
  Result,
  Script,
  Sentence,
  Tactic,
  atomic,
  pure,
} from "./syntax";

export type Error =
  | { type: "atomic_failure"; atomic: atomic; level: number }
  | { type: "tactic_failure"; tactic: Tactic }
  | { type: "out_of_fuel" };

function makeSentence(atomic: string): Sentence {
  return { type: "one", body: { type: "opaque", atomic: atomic } };
}

function printError(e: Error): Sentence | Comment {
  switch (e.type) {
    case "atomic_failure":
      return makeSentence(`Fail ${e.atomic}`);
    case "tactic_failure":
      return makeSentence(`Fail ${untactic(e.tactic)}`);
    case "out_of_fuel":
      return { type: "comment", body: "ran out of fuel" };
  }
}

type Hole = { type: "hole"; goal: goal };
type Node = { type: "node"; goal: goal; atomic: atomic; children: Tree[] };
type Failed = { type: "failed"; goal: goal; error: Error };
type Trace = { type: "trace"; trace: Tree[]; head: Tree };
export type Tree = Hole | Node | Failed | Trace;

type functype = (goal: goal) => Promise<Result<Tree>>;

export function lengthTree(r: Tree): number {
  switch (r.type) {
    case "hole":
      return 1;
    case "node":
      return r.children.map(lengthTree).reduce((a, b) => a + b, 0);
    case "failed":
      return 1;
    case "trace":
      return lengthTree(r.head);
  }
}

const admit: Sentence = makeSentence("admit");

export function leafGoals(r: Tree): goal[] {
  switch (r.type) {
    case "hole":
      return [r.goal];
    case "node":
      return r.children.map(leafGoals).flat(1);
    case "failed":
      return [r.goal];
    case "trace":
      return leafGoals(r.head);
  }
}

function failedTree(r: Tree): boolean {
  switch (r.type) {
    case "hole":
      return false;
    case "node":
      return r.children.some(failedTree);
    case "failed":
      return true;
    case "trace":
      return failedTree(r.head);
  }
}

export function extractScriptTree(r: Tree): Script {
  function loop(r: Tree): Script {
    switch (r.type) {
      case "hole":
        return [admit];
      case "node":
        const atomics: Script = [];
        atomics.push(makeSentence(r.atomic));
        const branches = r.children.length > 1;
        for (const child of r.children) {
          const catomics = loop(child);
          branches
            ? atomics.push({ type: "focus", block: catomics })
            : atomics.push.apply(atomics, catomics);
        }
        return atomics;
      case "failed":
        return [printError(r.error), admit];
      case "trace":
        const commented: Script = failedTree(r.head)
          ? r.trace
              .slice()
              .reverse()
              .map(
                (r_) =>
                  ({
                    type: "comment",
                    body: "tried and failed to run: " + unscript(prettyTrace(r_)),
                  } as Comment)
              )
              .flat(1)
          : [];
        return [...commented, ...loop(r.head)];
    }
  }

  function prettyTrace(r: Tree): Script {
    switch (r.type) {
      case "node":
        return [makeSentence(r.atomic), ...r.children.map(prettyTrace).flat(1)];
      case "hole":
        return [];
      case "failed":
        if (r.error.type === "out_of_fuel") {
          return [];
        } else if (r.error.type === "atomic_failure") {
          return [makeSentence(r.error.atomic)];
        } else {
          return [{ type: "one", body: r.error.tactic }];
        }
      case "trace":
        const commented: Script = r.trace
          .slice()
          .reverse()
          .map(prettyTrace)
          .flat(1);
        return [...commented, ...prettyTrace(r.head)];
    }
  }
  return loop(r);
}

export async function applyEachTree(
  fs: functype[],
  r: Tree
): Promise<Result<Tree>> {
  async function aux(
    fs: functype[],
    r: Tree
  ): Promise<Result<[functype[], Tree]>> {
    switch (r.type) {
      case "hole":
        return (await fs[0](r.goal)).fmap((r_) => [fs.slice(1), r_]);
      case "node":
        return (await aux_list(fs, r.children)).fmap(([fs_, rs_]) => [
          fs_,
          { ...r, children: rs_ },
        ]);
      case "failed":
        return pure([fs.slice(1), r]);
      case "trace":
        return (await aux(fs, r.head)).fmap(([fs_, r_]) => [
          fs_,
          { ...r, head: r_ },
        ]);
    }
  }

  async function aux_list(
    fs: functype[],
    rs: Tree[]
  ): Promise<Result<[functype[], Tree[]]>> {
    if (rs.length === 0) {
      return pure([fs, rs]);
    }

    return (await aux(fs, rs[0])).bindA(async ([fs_, r_]) =>
      (await aux_list(fs_, rs.slice(1))).bindA(async ([fs__, rs__]) =>
        pure([fs__, [r_, ...rs__]])
      )
    );
  }

  return (await aux(fs, r)).fmap((fsr) => fsr[1]);
}

export async function applyAllTree(
  f: functype,
  r: Tree
): Promise<Result<Tree>> {
  const fs = Array(lengthTree(r)).fill(f);
  return applyEachTree(fs, r);
}

export async function applyNthTree(
  f: functype,
  n: number,
  r: Tree
): Promise<Result<Tree>> {
  const treeid = (g: goal) =>
    pure({
      type: "hole",
      goal: g,
    });
  const fs = [
    ...Array(n - 1).fill(treeid),
    f,
    ...Array(lengthTree(r) - n).fill(treeid),
  ];
  return applyEachTree(fs, r);
}
