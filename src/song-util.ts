import { cpoint, PatUse, LoopEndpoint } from './types';

export type SongMouseState =
  | { t: "hover", mp: cpoint | null }
  | { t: "down", orig: cpoint, now: cpoint | null }
  | { t: "dragPat", orig: cpoint, now: cpoint | null, patUse: PatUse, patIx: number }
  | { t: "resizePat", orig: cpoint, now: cpoint | null, patUse: PatUse, patIx: number }
  | { t: "moveLoopEndpoint", orig: cpoint, now: cpoint | null, orig_val: number, which: LoopEndpoint }

export type SongMode = {t: "editSong", mouseState: SongMouseState }
