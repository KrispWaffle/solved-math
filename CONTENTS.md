# Contents

## Results

| Result | Written proof | Formal proof | Scope and prior work | Direct check |
|---|---|---|---|---|
| [Lee–Sah cluster-poset heights](results/lee-sah-cluster-height/README.md) | [Uniform limit shape](results/lee-sah-cluster-height/PROOF.md) | [Full conjecture and exponential bound](lean/SolvedMath/ClusterLimit.lean) | [Scope and review](results/lee-sah-cluster-height/AUDIT.md) | [Exact rank distributions](results/lee-sah-cluster-height/verify.py) |
| [Higher inversion limits for 1324](results/higher-inversion-limits/README.md) | [All finite bases](results/higher-inversion-limits/PROOF.md) · [Complete pair classification](results/higher-inversion-limits/CLASSIFICATION.md) · [Five tertiary series](results/higher-inversion-limits/TERTIARY-SERIES.md) | [Signed coefficients and source implication](lean/SolvedMath/HigherInversionClassification.lean) · [Maximum split](lean/SolvedMath/HigherInversionComponents.lean) · [All tertiary coefficients](lean/SolvedMath/HigherInversionSeries.lean) | [Priority and independent review](results/higher-inversion-limits/AUDIT.md) | [Pattern and slope certificates](results/higher-inversion-limits/verify.py) |
| [Stable inversion counts for 1243](results/stable-inversion-enumeration/README.md) | [Partition formula and finite-length refinement](results/stable-inversion-enumeration/PROOF.md) | [Bijection and source theorem](lean/SolvedMath/StableInversionPartitions.lean) | [Prior work and independent review](results/stable-inversion-enumeration/AUDIT.md) | [Partitions, insertion histories and literal permutations](results/stable-inversion-enumeration/verify.py) |
| [Attainable derangement limits](results/derangement-limit-spectrum/README.md) | [Full spectrum](results/derangement-limit-spectrum/PROOF.md) · [Polynomial growth and parity](results/derangement-limit-spectrum/POLYNOMIAL-CLASSES.md) · [Prescribed growth and the sum-closed upper ray](results/derangement-limit-spectrum/PRESCRIBED-GROWTH.md) | [Direct and skew sums](lean/SolvedMath/DerangementSpectrum.lean) · [Endpoints and interpolation](lean/SolvedMath/DerangementEndpoints.lean) · [Every rational witness](lean/SolvedMath/DerangementRationals.lean) · [Displacement and digit expansion](lean/SolvedMath/DerangementGrowth.lean) | [Scope and independent review](results/derangement-limit-spectrum/AUDIT.md) | [Exact checks](results/derangement-limit-spectrum/verify.py) |
| [Distinct patterns in a random permutation](results/distinct-random-permutation-patterns/README.md) | [Exact mean](results/distinct-random-permutation-patterns/PROOF.md) · [Limiting distribution](results/distinct-random-permutation-patterns/LIMIT-LAW.md) · [Full length profile](results/distinct-random-permutation-patterns/UNIFORM-PROFILE.md) · [Deletion deficits](results/distinct-random-permutation-patterns/EDGE-LENGTHS.md) | [Occurrence classes](lean/SolvedMath/RandomPatternClasses.lean) · [Moment implication](lean/SolvedMath/RandomPatternMoments.lean) · [Plot displacements](lean/SolvedMath/RandomPatternDisplacements.lean) | [Scope and review](results/distinct-random-permutation-patterns/AUDIT.md) | [Exact small orders](results/distinct-random-permutation-patterns/verify.py) |
| [Periodic set-valued tableaux](results/periodic-set-valued-tableaux/README.md) | [Transfer](results/periodic-set-valued-tableaux/PROOF.md) · [Asymptotics](results/periodic-set-valued-tableaux/ASYMPTOTICS.md) | [Common recurrence](lean/SolvedMath/TableauRecurrence.lean) · [Literal-coordinate obstruction](lean/SolvedMath/StripCoordinates.lean) | [Source and review](results/periodic-set-valued-tableaux/AUDIT.md) | [Physical word counts](results/periodic-set-valued-tableaux/verify.py) |
| [Pattern-poset separators](results/pattern-poset-separator/README.md) | [General classification](results/pattern-poset-separator/CLASSIFICATION.md) · [Specific separator](results/pattern-poset-separator/PROOF.md) | [Classification](lean/SolvedMath/SeparatorClassification.lean) · [Family](lean/SolvedMath/PatternSeparator.lean) | [Classification audit](results/pattern-poset-separator/CLASSIFICATION-AUDIT.md) · [Family audit](results/pattern-poset-separator/AUDIT.md) | [Rank test](results/pattern-poset-separator/classification.py) · [Window order](results/pattern-poset-separator/verify.py) |

## Archive

| Later derivation | Written proof | Scope and prior work | Direct check |
|---|---|---|---|
| [Big descents](archive/big-descents/README.md) | [Tableau formula](archive/big-descents/PROOF.md) | [Audit](archive/big-descents/AUDIT.md) | [Fundamental coefficients](archive/big-descents/verify.py) |
| [Packing cutoff](archive/packing-cutoff/README.md) | [Delayed divergence](archive/packing-cutoff/PROOF.md) | [Audit](archive/packing-cutoff/AUDIT.md) | [Packing counts](archive/packing-cutoff/verify.py) |

## Project records

- [Research log](docs/research-log.md) records the derivations and prior-work searches.
- [Lean status](docs/lean-status.md) lists the theorem declarations and how to reproduce the checks.
- [History](HISTORY.md) dates the entries and corrections.
