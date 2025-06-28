export type atomic = string;

type Opaque = {
  type: "opaque";
  atomic: atomic;
  loc?: number;
};
type Semicolon = {
  type: "semicolon";
  left: Tactic;
  right: Tactic;
  loc?: number;
};
type Dispatch = {
  type: "dispatch";
  left: Tactic;
  right: Tactic[];
  loc?: number;
};
type First = {
  type: "first";
  body: Tactic[];
  loc?: number;
};
type Progress = {
  type: "progress";
  body: Tactic;
  loc?: number;
};
type Try = {
  type: "try";
  body: Tactic;
  loc?: number;
};
type Repeat = {
  type: "repeat";
  body: Tactic;
  loc?: number;
};
type Auto = {
  type: "auto";
  loc?: number;
};
type Eauto = {
  type: "eauto";
  loc?: number;
};
export type Match = {
  type: "match";
  branches: [string, Tactic][];
};
type Empty = { type: "empty" };

// internal only:
export type TVar = { type: "tvar"; var: string };
type Fix = { type: "fix"; binder: TVar; body: Tactic };

export type Tactic =
  | Empty
  | Opaque
  | Semicolon
  | Dispatch
  | First
  | Progress
  | Fix
  | TVar
  // derived forms:
  | Try
  | Repeat
  // other:
  | Match
  | Auto
  | Eauto;

export type One = { type: "one"; body: Tactic };
export type Nth = { type: "nth"; n: number; body: Tactic };
export type All = { type: "all"; body: Tactic };

export type Sentence = One | Nth | All;

export type Focus = { type: "focus"; block: Script };

export type Comment = { type: "comment"; body: string };

export type Script = (Sentence | Focus | Comment)[];

export class Result<T> {
  fmap<U>(func: (t: T) => U): Result<U> {
    return this.bind((t) => pure(func(t)));
  }

  bind<U>(func: (t: T) => Result<U>): Result<U> {
    throw new Error("abstract");
  }

  async bindA<U>(func: (t: T) => Promise<Result<U>>): Promise<Result<U>> {
    throw new Error("abstract");
  }

  failed(): boolean {
    throw new Error("abstract");
  }
}

export class Yes<T> extends Result<T> {
  t: T;
  level: number | null;

  constructor(t: T, level: number | null) {
    super();
    this.t = t;
    this.level = level;
  }

  transform<U>(mu: Result<U>): Result<U> {
    if (mu instanceof No) {
      return mu;
    } else {
      const yu = mu as Yes<U>;
      const level = this.level === null ? yu.level : this.level;
      return new Yes(yu.t, level);
    }
  }

  bind<U>(func: (t: T) => Result<U>): Result<U> {
    const mu = func(this.t);
    return this.transform(mu);
  }

  async bindA<U>(func: (t: T) => Promise<Result<U>>): Promise<Result<U>> {
    const mu = await func(this.t);
    return this.transform(mu);
  }

  failed(): boolean {
    return this.level !== null;
  }

  decr(): number | null {
    if (this.level !== null) {
      return Math.max(this.level - 1, 0);
    } else {
      return this.level;
    }
  }
}

export class No<T> extends Result<T> {
  level: number;

  constructor(level: number) {
    super();
    this.level = level;
  }

  bind<U>(func: (t: T) => Result<U>): Result<U> {
    return new No(this.level);
  }

  async bindA<U>(func: (t: T) => Promise<Result<U>>): Promise<Result<U>> {
    return new No(this.level);
  }

  failed() {
    return true;
  }
}

export function pure<T>(t: T): Result<T> {
  return new Yes(t, null);
}

export function subst(x: TVar, t1: Tactic, t2: Tactic): Tactic {
  switch (t1.type) {
    case "tvar":
      if (x === t1) {
        return t2;
      } else {
        return t1;
      }
    case "semicolon":
      return {
        ...t1,
        left: subst(x, t1.left, t2),
        right: subst(x, t1.right, t2),
      };
    case "dispatch":
      return {
        ...t1,
        left: subst(x, t1.left, t2),
        right: t1.right.map((t) => subst(x, t, t2)),
      };
    case "first":
      return {
        ...t1,
        body: t1.body.map((t) => subst(x, t, t2)),
      };
    case "fix":
      if (x === t1.binder) {
        return t1;
      } else {
        return { ...t1, body: subst(x, t1.body, t2) };
      }
    case "progress":
    case "try":
    case "repeat":
      return { ...t1, body: subst(x, t1.body, t2) };
    case "match":
      return {
        ...t1,
        branches: t1.branches.map((b) => [b[0], subst(x, b[1], t2)]),
      };
    case "opaque":
    case "empty":
    case "auto":
    case "eauto":
      return t1;
  }
}
