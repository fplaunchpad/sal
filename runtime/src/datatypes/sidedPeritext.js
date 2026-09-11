// Explicit comparison configurations. The production `peritext` export now
// uses the same unified sided kernel as `sidedPeritextReleaseCandidate`.

import { makePeritext } from './peritext.js';
import {
  sidedEmbedRGAExperimental,
  sharedSidedEmbedRGAExperimental,
} from './sidedEmbedRGA.js';
import { sidedEmbedRGAReleaseCandidate } from './unifiedSidedEmbedRGA.js';

export const sidedPeritextExperimental = makePeritext(sidedEmbedRGAExperimental);
export const sharedSidedPeritextExperimental = makePeritext(sharedSidedEmbedRGAExperimental);
export const sidedPeritextReleaseCandidate = makePeritext(sidedEmbedRGAReleaseCandidate);
