# Capacity Atlas: causal encoder state

A Lean proof of Shannon's capacity formula for a finite DMC whose encoder observes the iid state causally and whose decoder observes only channel outputs:

`C = max I(T; Y)`, where `T` is a function from states to input symbols and the strategy channel averages `q(s) W(y | T(s), s)`.

Encoders may use the entire past and current state prefix. They receive no output feedback. The model uses deterministic codes, uniform messages, vanishing average error, and codes at every sufficiently large blocklength.

The direct proof embeds ordinary strategy-channel codes while preserving their exact physical block law, rate, and average error. The converse splits off the last use, applies a finite entropy extension inequality, inducts over arbitrary causal policies, and uses Fano's inequality. Compactness supplies an optimizing strategy distribution.

The Atlas model and neutral reusable APIs are pinned in `lakefile.toml`. `CapacityAtlasCausal.capacityCertificate` proves the canonical proposition `CapacityAtlas.Channel.causalStateCapacityStatement` directly. The audit checks all transitive proof axioms and compares the certificate type against the full canonical proposition with its parameters.

Run `lake --wfail build` and `lake exe capacity_causal_audit`.

Primary source: C. E. Shannon, [Channels with Side Information at the Transmitter](https://doi.org/10.1147/rd.24.0289), IBM Journal of Research and Development 2(4), 289–293 (1958), unnumbered strategy-channel theorem. The original text was visually checked in the Collected Papers reproduction, pp.274–276.

AI assistance was used for research, implementation, and review. Human review of statement faithfulness and literature attribution is required before merge.

License: Apache-2.0.
