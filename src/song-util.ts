import { cpoint, PatUse } from './types';

export type SongMouseState =
  | { t: "hover", mp: cpoint | null }
  | { t: "down", orig: cpoint, now: cpoint | null }
  | { t: "dragPat", orig: cpoint, now: cpoint | null, patUse: PatUse, patIx: number }
  | { t: "resizePat", orig: cpoint, now: cpoint | null, patUse: PatUse, patIx: number }

export type SongMode = {t: "editSong", mouseState: SongMouseState }
