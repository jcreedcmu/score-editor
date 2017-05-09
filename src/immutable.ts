import { fromJS as _fromJS } from 'immutable';

// some phantom types
export type Immutable<T> = {
   [P in keyof T]: Immut<T[P]>;
};
class Path<T, U> { private _className = "Path"; }
class Immut<T> { private _className = "Immutable"; }

function getPath<T, U>(f: (x: T) => U): Path<T, U> {
  const path: any = [];
  const proxy = new Proxy({}, {
	 get: (target: {}, name: PropertyKey) => {
		path.push(name);
		return proxy;
	 }
  });
  f(proxy as T);
  return path as Path<T, U>;
}

export function fromJS<T>(x: T): Immutable<T> {
  return _fromJS(x);
}

// this will break on primitives!
export function toJS<T>(x: Immutable<T>): T {
  return (x as any).toJS();
}

export function getIn<T, U>(x: Immutable<T>, pf: (y: T) => U): Immutable<U> {
  return (x as any).getIn(getPath(pf));
}

export function get<T, K extends keyof T>(x: Immutable<T>, key: K): Immutable<T[K]> {
  return (x as any).get(key);
}

export function setIn<T, U>(x: Immutable<T>, pf: (y: T) => U, val: Immutable<U>): Immutable<T> {
  return (x as any).setIn(getPath(pf), val);
}

export function set<T, K extends keyof T>(x: Immutable<T>, key: K, val: Immutable<T[K]>): Immutable<T> {
  return (x as any).set(key, val);
}

export function updateIn<T, U>(x: Immutable<T>, pf: (y: T) => U, f: (z: Immutable<U>) => Immutable<U>): Immutable<T> {
  return (x as any).updateIn(getPath(pf), f);
}

export function update<T, K extends keyof T>(x: Immutable<T>, key: K, f: (z: Immutable<T[K]>) => Immutable<T[K]>): Immutable<T> {
  return (x as any).update(key, f);
}
