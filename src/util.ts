// x is a floating point number. We want to return an int, but have
// the function feel reasonably responsive even if x isn't that far
// from zero.
export function augment_and_snap(x: number) {
  const sgn = x > 0 ? 1 : -1;
  const abs = Math.abs(x);
  const snap = Math.floor(abs+0.5);
  return snap * sgn;
}

export function findLast<T>(xs: T[], f: (x: T) => boolean): T | undefined {
  for (let i = xs.length - 1; i >= 0; i--) {
	 if (f(xs[i])) return xs[i];
  }
  return undefined;
}

export function findLastIndex<T>(xs: T[], f: (x: T) => boolean): number {
  for (let i = xs.length - 1; i >= 0; i--) {
	 if (f(xs[i])) return i;
  }
  return -1;
}

export type FindInfo<T> = { item: T, index: number }
export function findLastOpt<T, U>(xs: T[], f: (x: T) => (U | undefined)): FindInfo<U> | undefined {
  for (let i = xs.length - 1; i >= 0; i--) {
	 let item = f(xs[i]);
	 if (item != undefined) return {item, index: i };
  }
  return undefined;
}
