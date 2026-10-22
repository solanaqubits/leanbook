# v0.7.43: Checked quota cursor snapshots

This scoped release exports epsilon239, CryptoHiddenScalarQuotaSnapshotContract.
241 direct MasterSuite imports and 285 Lean sources are byte-identical to the
pinned private formal sources.

QuotaCursorSnapshot stores a bound and a list of rational values. restoreCursor?
checks length, runs startQuotaSearch through the saved bound, rejects any early
success, and compares the saved row with the certified exhausted cursor.
The exact success criterion is ValidSnapshot n p j eps s together with
snapshotCursor c = s. Exact cursor round trip and correctness of subsequent
continuation are proved for arbitrary rational profiles and tolerances.
Full equality with a cold resumed search requires a nonshrinking bound;
scalar correctness also holds for smaller requested windows.

22 IO scenarios and 29 Lean examples cover altered or incorrectly sized rows,
prefix success despite final rejection, calibrations 4/6, arbitrary profiles,
negative tolerances and exact restored cursor states.

This contract concerns typed in-memory snapshots. Byte encoding, canonical
external fraction parsing, authentication and profile transfer are separate.
Equality of rational values such as 2/4 and 1/2 is not an external codec claim.
The explicit qutrit Spec build remains in place.

Lake remains 0.7.1. Full public beta basis
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1) is unchanged.
Independent scoped checks do not create a new full beta checkpoint.
