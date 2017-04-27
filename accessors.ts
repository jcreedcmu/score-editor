import { AppState, Pattern, Note, Mode } from './types';
import { Immutable as Im, get, getIn, setIn, updateIn, fromJS, toJS } from './immutable';

export function updateCurrentNotes(state: Im<AppState>, f: (x: Im<Note[]>) => Im<Note[]>): Im<AppState> {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return state; // maybe console.log in this case?
  return updateIn(state, x => x.score.patterns[pat].notes, f);
}

export function getCurrentPattern(state: Im<AppState>): string | undefined {
  const mode = toJS<Mode>(get(state, "mode"));
  switch(mode.t) {
  case "editPattern": return mode.patName;
  default: return undefined;
  }
}

export function currentPatUndefined(state: Im<AppState>): boolean {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const p = getIn(state, x => x.score.patterns[pat])
  return p == undefined
}

export function _getCurrentNotes(state: Im<AppState>): Note[] | undefined {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const notes = getIn(state, x => x.score.patterns[pat].notes)
  if (notes == undefined) return undefined; // this is definitely a non-exceptional case
  return toJS(notes);
}

// ad hoc cache, not sure if I should be doing something smarter
let lastState = null;
let lastAnswer = null;
export function getCurrentNotes(state: Im<AppState>): Note[] | undefined {
  if (state != lastState) {
    lastState = state; lastAnswer = _getCurrentNotes(lastState);
  }
  return lastAnswer;
}

export function setCurrentNotes(state: Im<AppState>, notes: Note[]): Im<AppState> {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  return setIn(state, x => x.score.patterns[pat].notes, fromJS(notes))
}

export function getCurrentPat(state: Im<AppState>): Pattern | undefined {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const p = getIn(state, x => x.score.patterns[pat])
  if (p == undefined) return undefined; // this is definitely a non-exceptional case
  return toJS(p);
}

export function setCurrentPat(state: Im<AppState>, p: Pattern): Im<AppState> {
  const pat = getCurrentPattern(state);
  return setIn(state, x => x.score.patterns[pat], fromJS(p))
}
