import { Instrument, Pattern } from './types'

export function getPatInst(patName: string, p: Pattern): Instrument {
  return patName.match(/drum/) ? 'drums' : 'sine';
}
