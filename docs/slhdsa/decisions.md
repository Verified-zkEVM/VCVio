# Decision log

The authoritative state is machine-readable in `matrices/decisions.csv`. S00 proposes the profile
and sequencing choices; it does not silently record maintainer approval.

| ID | Status | Decision | Approval/evidence | Session |
|---|---|---|---|---|
| D-001 | PROPOSED | FIPS205-12 is the normative implementation target | Approver unassigned; `scope.md` | S00 |
| D-002 | PROPOSED | Keep `LEGACY-SHA2-128-24` as the single current-code reduced subprofile, distinct from `SP800-230-IPD-6SET` | Approver unassigned; `scope.md` | S00 |
| D-003 | PROPOSED | Treat C13 as a separate profile pending disposition | Approver unassigned; `scope.md` | S00/S18 |
| D-004 | PROPOSED | Freeze security/oracle architecture before construction refactors | Approver unassigned; `lean-blueprint.md` | S00/S02 |
| D-005 | PROPOSED | Reports are secondary and primary sources control | Approver unassigned; `source-ledger.md` | S00 |
| D-006 | PROPOSED | Select exact master theorem/notions and classical/QROM semantics | Approver unassigned; declaration comparison required | S02 |
| D-007 | BLOCKED | Select Ethereum deployment/refinement target | Approver unassigned; repository/commit/ABI absent | S19 |
| D-008 | PROPOSED | C13: separate support, core merge, or deprecate | Approver unassigned; pinned sources/owner choice required | S18 |

Statuses are `proposed`, `accepted`, `rejected`, `blocked`, or `superseded`. `accepted` requires a
named approver and evidence in the CSV. Supersession appends a new linked row; history is not erased.
