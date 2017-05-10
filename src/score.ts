// got these from 'overboard'
// https://twitter.com/jcreed/status/851457146852184065
// beepbox export to json then
// jq -c '[.channels[0,1,2].patterns[1].notes[]|{pitch:.pitches[0], time: [.points[0].tick, .points[1].tick]}]'  /tmp/BeepBox-Song.json

import { Score } from './types';
export const score: Score = {
  "loop_start": 0,
  "loop_end": 64,
  "next_id": 167,
  "duration": 65,
  "seconds_per_tick": 0.09,
  "song": [
    {
      "lane": 1,
      "patName": "default",
      "start": 0,
      "duration": 64
    },
    {
      "lane": 0,
      "patName": "drums",
      "start": 0,
      "duration": 64
    }
  ],
  "patterns": {
    "drums": {
      "length": 32,
      "notes": [
        {
          "pitch": 48,
          "time": [
            0,
            2
          ],
          "id": "n101"
        },
        {
          "pitch": 60,
          "time": [
            8,
            10
          ],
          "id": "n103"
        },
        {
          "pitch": 60,
          "time": [
            24,
            26
          ],
          "id": "n104"
        },
        {
          "pitch": 48,
          "time": [
            14,
            16
          ],
          "id": "n105"
        },
        {
          "pitch": 48,
          "time": [
            20,
            22
          ],
          "id": "n106"
        },
        {
          "pitch": 48,
          "time": [
            22,
            24
          ],
          "id": "n107"
        },
        {
          "pitch": 64,
          "time": [
            0,
            1
          ],
          "id": "n108"
        },
        {
          "pitch": 64,
          "time": [
            4,
            5
          ],
          "id": "n109"
        },
        {
          "pitch": 64,
          "time": [
            8,
            10
          ],
          "id": "n111"
        },
        {
          "pitch": 64,
          "time": [
            12,
            13
          ],
          "id": "n112"
        },
        {
          "pitch": 64,
          "time": [
            16,
            17
          ],
          "id": "n113"
        },
        {
          "pitch": 64,
          "time": [
            20,
            21
          ],
          "id": "n114"
        },
        {
          "pitch": 64,
          "time": [
            24,
            26
          ],
          "id": "n115"
        },
        {
          "pitch": 64,
          "time": [
            28,
            29
          ],
          "id": "n116"
        }
      ]
    },
    "default": {
      "length": 32,
      "notes": [
        {
          "pitch": 60,
          "time": [
            0,
            1
          ],
          "id": "n117"
        },
        {
          "pitch": 63,
          "time": [
            2,
            3
          ],
          "id": "n118"
        },
        {
          "pitch": 63,
          "time": [
            4,
            8
          ],
          "id": "n119"
        },
        {
          "pitch": 60,
          "time": [
            12,
            13
          ],
          "id": "n120"
        },
        {
          "pitch": 63,
          "time": [
            14,
            15
          ],
          "id": "n121"
        },
        {
          "pitch": 65,
          "time": [
            16,
            17
          ],
          "id": "n122"
        },
        {
          "pitch": 66,
          "time": [
            17,
            18
          ],
          "id": "n123"
        },
        {
          "pitch": 65,
          "time": [
            18,
            20
          ],
          "id": "n124"
        },
        {
          "pitch": 63,
          "time": [
            20,
            21
          ],
          "id": "n125"
        },
        {
          "pitch": 60,
          "time": [
            21,
            26
          ],
          "id": "n126"
        },
        {
          "pitch": 48,
          "time": [
            0,
            2
          ],
          "id": "n127"
        },
        {
          "pitch": 55,
          "time": [
            4,
            6
          ],
          "id": "n132"
        },
        {
          "pitch": 55,
          "time": [
            10,
            12
          ],
          "id": "n133"
        },
        {
          "pitch": 55,
          "time": [
            12,
            16
          ],
          "id": "n134"
        },
        {
          "pitch": 51,
          "time": [
            10,
            12
          ],
          "id": "n135"
        },
        {
          "pitch": 51,
          "time": [
            12,
            14
          ],
          "id": "n136"
        },
        {
          "pitch": 51,
          "time": [
            4,
            6
          ],
          "id": "n137"
        },
        {
          "pitch": 48,
          "time": [
            10,
            12
          ],
          "id": "n139"
        },
        {
          "pitch": 58,
          "time": [
            26,
            28
          ],
          "id": "n140"
        },
        {
          "pitch": 60,
          "time": [
            28,
            32
          ],
          "id": "n141"
        },
        {
          "pitch": 48,
          "time": [
            20,
            22
          ],
          "id": "n142"
        },
        {
          "pitch": 53,
          "time": [
            22,
            23
          ],
          "id": "n143"
        },
        {
          "pitch": 54,
          "time": [
            23,
            24
          ],
          "id": "n146"
        },
        {
          "pitch": 53,
          "time": [
            24,
            26
          ],
          "id": "n147"
        },
        {
          "pitch": 51,
          "time": [
            26,
            28
          ],
          "id": "n148"
        },
        {
          "pitch": 50,
          "time": [
            28,
            30
          ],
          "id": "n149"
        },
        {
          "pitch": 48,
          "time": [
            30,
            32
          ],
          "id": "n150"
        },
        {
          "pitch": 70,
          "time": [
            4,
            5
          ],
          "id": "n152"
        },
        {
          "pitch": 67,
          "time": [
            2,
            3
          ],
          "id": "n160"
        },
        {
          "pitch": 67,
          "time": [
            6,
            7
          ],
          "id": "n162"
        },
        {
          "pitch": 65,
          "time": [
            8,
            9
          ],
          "id": "n163"
        },
        {
          "pitch": 67,
          "time": [
            10,
            11
          ],
          "id": "n164"
        },
        {
          "pitch": 65,
          "time": [
            12,
            13
          ],
          "id": "n165"
        }
      ]
    }
  }
}
