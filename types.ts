import { fromJS, Immutable } from './immutable';

export type Note = { pitch: number, time: [number, number] };

export type MouseAction =
  | { t: "Mousemove"; mpoint: mpoint; }
  | { t: "Mousedown"; mpoint: mpoint; }
  | { t: "Mouseup" }
  | { t: "Mouseleave" }

export type Action =
  MouseAction
  | { t: "Play"; score: Score; }
  | { t: "Vscroll"; top: number; }
  | { t: "SetCurrentPlaybackTime"; v: number }
  | { t: "Key", key: string }
  | { t: "ExecMinibuf", cmd: string }
  | { t: "SetMinibuf", v: string }
  | { t: "EditSong" }
  | { t: "EditPat", patName: string }

export type Pattern = {
  length: number,
  notes: Note[],
};

export type PatUse = {
  patName: string,
  start: number,
  duration: number,
}

export type Score = {
  duration: number, // ticks
  seconds_per_tick: number,
  song: PatUse[],
  patterns: {[P in string]: Pattern},
};

export type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas

// XXX rename 'time' to 'ticks'
export type mpoint = { pitch: number, time: number } & cpoint // point also in "musical coordinates"


export type RollMouseState =
  | { t: "hover", mp: mpoint | null }
  | { t: "down", orig: mpoint, now: mpoint | null }
  | { t: "resizeNote", fromRight: boolean, orig: mpoint, now: mpoint | null,
		note: Note, noteIx: number }

export type Mode =
  | {t: "editPattern", patName: string, mouseState: RollMouseState }
  | {t: "editSong" }

export type BaseState = {
  offsetTicks: number | null,
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
  previewNote: null,
  score: {duration: 32,
			 seconds_per_tick: 0.1,
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
