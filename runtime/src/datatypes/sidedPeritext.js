// Explicit experimental Peritext configurations. The production `peritext`
// export remains on the one-sided EmbedRGA until the benchmark promotion gate.

import { makePeritext } from './peritext.js';
import {
  sidedEmbedRGAExperimental,
  sharedSidedEmbedRGAExperimental,
} from './sidedEmbedRGA.js';
import { sidedEmbedRGAReleaseCandidate } from './unifiedSidedEmbedRGA.js';

export const sidedPeritextExperimental = makePeritext(sidedEmbedRGAExperimental);
export const sharedSidedPeritextExperimental = makePeritext(sharedSidedEmbedRGAExperimental);
export const sidedPeritextReleaseCandidate = makePeritext(sidedEmbedRGAReleaseCandidate);
