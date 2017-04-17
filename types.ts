export type Note = { pitch: number, time: [number, number] };

// the interface names should probably not be needed outside this
// module, only the tag names, which I'm by convention keeping the
// same as them.
interface SetHover {
  t: "SetHover";
  mpoint: mpoint | null;
}
interface CreateNote {
  t: "CreateNote";
  note: Note;
}
interface DeleteNote {
  t: "DeleteNote";
  note: Note;
}
interface Play {
  t: "Play";
  score: Score;
}
interface IncrementGridSize {
  t: "IncrementGridSize";
  by: number;
}
interface SetCurrentPlaybackTime { t: "SetCurrentPlaybackTime", v: number }
export type Action =
  SetHover
  | CreateNote
  | DeleteNote
  | Play
  | SetCurrentPlaybackTime
  | IncrementGridSize;

export type Score = {
  duration: number, // ticks
  seconds_per_tick: number,
  notes: Note[],
};

// XXX rename 'time' to 'ticks'
export type mpoint = { pitch: number, time: number } // point in "musical coordinates"
export type cpoint = { x: number, y: number } // point measured in pixels from the topleft of the canvas

export type BaseState = {
  offsetTicks: number | null,
  mouseHover: mpoint | null,
  score: Score,
  gridSize: number,
};

export type DerivedState = {
  previewNote: Note | null,
}

export type AppState = BaseState & DerivedState;
