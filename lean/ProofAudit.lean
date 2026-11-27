import SolvedMath

open SolvedMath.PatternSeparator

/-- info: 'SolvedMath.PatternSeparator.SeparatedOverlap.separator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SeparatedOverlap.separator

/-- info: 'SolvedMath.PatternSeparator.bks_overlap_two_separator' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bks_overlap_two_separator

/-- info: 'SolvedMath.PatternSeparator.Compatible.weak_iff_threshold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Compatible.weak_iff_threshold

/-- info: 'SolvedMath.PatternSeparator.Compatible.strict_asymmetric' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Compatible.strict_asymmetric

/-- info: 'SolvedMath.PatternSeparator.bks_separator_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bks_separator_at

/-- info: 'SolvedMath.PatternSeparator.bks_separator_always' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bks_separator_always
