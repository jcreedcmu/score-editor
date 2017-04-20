// could use immutablejs instead
export function updateIn<T>(obj: any, path: any[], f: (x: T) => T): any {
  const _go = ((obj: any, pi: number) =>
					pi == path.length ? f(obj) : {...obj, [path[pi]]: _go(obj[path[pi]], pi+1)});
  return _go(obj, 0);
}
