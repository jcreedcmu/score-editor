export type Note = { pitch: number, time: [number, number] };

export type MouseAction =
  | { t: "Mousemove"; mpoint: mpoint; }
  | { t: "Mousedown"; mpoint: mpoint; }
  | { t: "Mouseup" }
  | { t: "Mouseleave" }

export type Action =
  MouseAction
  | { t: "CreateNote"; note: Note; }
  | { t: "DeleteNote"; note: Note; }
  | { t: "Play"; score: Score; }
  | { t: "Vscroll"; top: number; }
  | { t: "SetCurrentPlaybackTime"; v: number }
  | { t: "Key", key: string }
  | { t: "ExecMinibuf", cmd: string }
  | { t: "SetMinibuf", v: string }

export type Score = {
  duration: number, // ticks
  seconds_per_tick: number,
  notes: Note[],
};

// XXX rename 'time' to 'ticks'
export type mpoint = { pitch: number, time: number } // point in "musical coordinates"
export type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas

export type MouseState =
  | { t: "hover", mp: mpoint | null }
  | { t: "down", orig: mpoint, now: mpoint | null }

export type BaseState = {
  offsetTicks: number | null,
  mouseState: MouseState,
  score: Score,
  gridSize: number,
  scrollOctave: number,
  minibufferVisible: boolean,
  minibuf: string,
};

export type DerivedState = {
  previewNote: Note | null,
}

export type AppState = BaseState & DerivedState;

export const initialState: AppState = {
  offsetTicks: null,
  mouseState: {t: "hover", mp: null},
  previewNote: null,
  score: {duration: 32, seconds_per_tick: 0.1, notes: []},
  gridSize: 4,
  scrollOctave: 3, /* in the range [0 .. 4] for now, higher numbers are lower pitch */
  minibufferVisible: false,
  minibuf: '',
};
