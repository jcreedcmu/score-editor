// could use immutablejs instead
export function updateIn<T>(obj: any, path: any[], f: (x: T) => T): any {
  const _go = function (obj: any, pi: number) {
	 if (pi == path.length) {
		return f(obj)
	 }
	 else {
		if (obj instanceof Array) {
		  const copy = [...obj];
		  copy.splice(path[pi], 1, _go(obj[path[pi]], pi+1));
		  return copy;
		}
		else {
		  return {...obj, [path[pi]]: _go(obj[path[pi]], pi+1)};
		}
	 }
  }
  return _go(obj, 0);
}
