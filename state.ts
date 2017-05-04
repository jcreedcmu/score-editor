import { PatUse, Score, Note, cpoint } from './types';
import { fromJS, Immutable } from './immutable';
import { RollMode } from './roll-util';
import { SongMode } from './song-util';

export type Mode =
  | RollMode
  | SongMode

export type BaseState = {
  offsetTicks: number | null,
  debugOffsetTicks: number | null,
  lastMouseDown?: Date,
  score: Score,
  mode: Mode,
  gridSize: number,
  noteSize: number,
  scrollOctave: number,
  minibufferVisible: boolean,
  minibuf: string,
};

export type DerivedState = {
  // XXX this belongs scoped to editpattern mode data I think?
  previewNote: Note | null,
}

export type AppState = BaseState & DerivedState;

const _initialState: AppState = {
  offsetTicks: null,
  debugOffsetTicks: null,
  previewNote: null,
  score: {duration: 32,
			 seconds_per_tick: 0.1,
			 next_id: 0,
			 patterns: {default: {length: 32, notes: []}},
			 song: []},
  gridSize: 1,
  noteSize: 1,
  scrollOctave: 3, /* in the range [0 .. 4] for now, higher numbers are lower pitch */
  minibufferVisible: false,
  minibuf: '',
  mode: {t: "editPattern", patName: "default", mouseState: {t: "hover", mp: null }},
};

export const initialState: Immutable<AppState> = fromJS(_initialState);
