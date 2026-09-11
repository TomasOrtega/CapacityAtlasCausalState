/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasCausal.Converse
import CapacityAtlas.Channels.CausalState

open CapacityAtlas

namespace CapacityAtlasCausal

/-- Certificate of the canonical Atlas proposition, with every model parameter preserved. -/
theorem capacityCertificate {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]
    [Nonempty X] (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    Channel.causalStateCapacityStatement state channels :=
  causalStateCapacity state channels

end CapacityAtlasCausal
