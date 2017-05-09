import { Pattern, Note, IdNote, Song } from './types';
import { AppState, Mode } from './state';
import { RollMode } from './roll-util';
import { Immutable as Im, get, getIn, set, setIn, updateIn, fromJS, toJS } from './immutable';

export function updateCurrentNotes(state: Im<AppState>, f: (x: Im<IdNote[]>) => Im<IdNote[]>): Im<AppState> {
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

export function _getCurrentNotes(state: Im<AppState>): IdNote[] | undefined {
  const pat = getCurrentPattern(state);
  if (pat == undefined) return undefined; // maybe console.log in this case?
  const notes = getIn(state, x => x.score.patterns[pat].notes)
  if (notes == undefined) return undefined; // this is definitely a non-exceptional case
  return toJS(notes);
}

// ad hoc cache, not sure if I should be doing something smarter
let lastState = null;
let lastAnswer = null;
export function getCurrentNotes(state: Im<AppState>): IdNote[] | undefined {
  if (state != lastState) {
    lastState = state; lastAnswer = _getCurrentNotes(lastState);
  }
  return lastAnswer;
}

export function setCurrentNotes(state: Im<AppState>, notes: IdNote[]): Im<AppState> {
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

export function updateCurrentPat(state: Im<AppState>, f: (x: Im<Pattern>) => Im<Pattern>): Im<AppState> {
  const pat = getCurrentPattern(state);
  return updateIn(state, x => x.score.patterns[pat], f)
}

export function getSong(state: Im<AppState>): Song {
  return toJS(getIn(state, x => x.score.song));
}

export function setSong(state: Im<AppState>, song: Song): Im<AppState> {
  return setIn(state, x => x.score.song, fromJS(song));
}

export function updateSong(state: Im<AppState>, f: (x: Im<Song>) => Im<Song>): Im<AppState> {
  return updateIn(state, x => x.score.song, f);
}

export function ensurePatternExists(state: Im<AppState>, patName: string): Im<AppState> {
  if (getIn(state, x => x.score.patterns[patName]) == undefined) {
	 return setIn(state, x => x.score.patterns[patName], fromJS({notes: [], length: 32}));
  }
  return state;
}

export function modeEditPattern(state: Im<AppState>, patName: string): Im<AppState> {
  const s = ensurePatternExists(state, patName);
  return set(s, 'mode', fromJS<RollMode>({t: "editPattern", patName,
																mouseState: {t: 'hover', mp: null}}));
}
