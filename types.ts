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
  | { t: "IncrementGridSize"; by: number; }
  | { t: "Vscroll"; top: number; }
  | { t: "SetCurrentPlaybackTime"; v: number }
  | { t: "ToggleMinibuf" }

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
};

export type DerivedState = {
  previewNote: Note | null,
}

export type AppState = BaseState & DerivedState;
