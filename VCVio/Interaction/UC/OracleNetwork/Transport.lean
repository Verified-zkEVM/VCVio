/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.OracleNetwork
public import PolyFun.Interaction.UC.RequestNetwork.Transport

/-!
# Transporting oracle FIFO executions

A bijection of client identities transports waiting continuations, ticketed traffic,
delivered transcripts, and schedules together. The generic polynomial transport theorem
preserves the service's monadic effects and their ordering.
-/

public section

namespace Interaction.UC.OracleNetwork

export RequestNetwork (emit_rename accept_rename deliver_rename step_rename run_rename)

end Interaction.UC.OracleNetwork
