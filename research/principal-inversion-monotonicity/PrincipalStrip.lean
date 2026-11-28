import LayeredStrip

namespace PrincipalInversionMonotonicity

open StableInversions (invCount)

/-- Classical avoidance on four positions of a rank word. -/
def Avoid1324 (w : List Nat) : Prop :=
  ∀ a b c d, [a,b,c,d].Sublist w → a < c → c < b → b < d → False

def Avoid4231 (w : List Nat) : Prop :=
  ∀ a b c d, [a,b,c,d].Sublist w → d < b → b < c → c < a → False

private theorem avoid_below_append {L R : List Nat}
    (left : Avoid4231 L) (right : Avoid4231 R) (below : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    Avoid4231 (L ++ R) := by
  intro a b c d hit db bc ca
  obtain ⟨x,y,e,hx,hy⟩ := List.sublist_append_iff.mp hit
  have pre : ([a,b,c,d].take x.length).Sublist L := by rw [e,List.take_left]; exact hx
  have suf : ([a,b,c,d].drop x.length).Sublist R := by rw [e,List.drop_left]; exact hy
  have len := congrArg List.length e
  simp at len
  by_cases empty : x.length = 0
  · exact right a b c d (by simpa [empty] using suf) db bc ca
  by_cases full : x.length = 4
  · exact left a b c d (by simpa [full] using pre) db bc ca
  have split : x.length = 1 ∨ x.length = 2 ∨ x.length = 3 := by omega
  rcases split with h | h | h <;>
    have bad := below a (pre.subset (by simp [h])) d (suf.subset (by simp [h])) <;>
    omega

theorem layered_avoids_4231 (ds : List Nat) (s : Nat) : Avoid4231 (layered s ds) := by
  induction ds generalizing s with
  | nil => simp [layered, Avoid4231]
  | cons e ds ih =>
    rw [layered]
    refine avoid_below_append ?_ (ih (s+e)) ?_
    · intro a b c d hit db bc ca
      have desc : (List.range' s e).reverse.Pairwise (· > ·) :=
        List.pairwise_reverse.mpr (List.pairwise_lt_range' (s := s) (n := e))
      have sub := List.Pairwise.sublist hit desc
      have cb := (List.pairwise_cons.mp (List.pairwise_cons.mp sub).2).1 c (by simp)
      omega
    · intro a ha b hb
      have al := (List.mem_range'_1.mp (List.mem_reverse.mp ha)).2
      have bl := (List.mem_range'_1.mp ((layered_permutation ds (s+e)).mem_iff.mp hb)).1
      omega

theorem reverse_avoidance (w : List Nat) : Avoid1324 w ↔ Avoid4231 w.reverse := by
  constructor
  · intro h a b c d hit db bc ca
    exact h d c b a (by simpa using List.reverse_sublist.mpr hit) db bc ca
  · intro h a b c d hit ac cb bd
    exact h d c b a (by simpa using List.reverse_sublist.mpr hit) ac cb bd

private theorem inversions_snoc (w : List Nat) (a : Nat) :
    invCount (w ++ [a]) = invCount w + w.countP (a < ·) := by
  induction w with
  | nil => simp [invCount]
  | cons b w ih =>
    by_cases h : a < b <;> simp [invCount, List.countP_append, h, ih] <;> omega

private theorem counts_around {a : Nat} (w : List Nat) (missing : a ∉ w) :
    w.countP (· < a) + w.countP (a < ·) = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have diff : a ≠ b := by intro e; exact missing (by simp [e])
    have tail := ih (fun h => missing (List.mem_cons_of_mem _ h))
    rcases lt_or_gt_of_ne diff with h | h
    · simp [h,Nat.not_lt_of_ge h.le]
      omega
    · simp [h,Nat.not_lt_of_ge h.le]
      omega

theorem reverse_inversions (w : List Nat) (distinct : w.Nodup) :
    invCount w.reverse + invCount w = triangular w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ⟨missing, nodup⟩ := List.nodup_cons.mp distinct
    have rest := ih nodup
    have crossed := counts_around w missing
    simp only [List.reverse_cons, inversions_snoc, List.countP_reverse, invCount,
      List.length_cons, triangular]
    omega

private theorem reverse_in_buckets {D E : List Nat → Prop}
    (reflection : ∀ w, D w ↔ E w.reverse) {n k j : Nat} (total : k + j = triangular n)
    {w : List Nat} (perm : w.Perm (List.range' 0 n)) :
    (w ∈ bucket D n k ↔ w.reverse ∈ bucket E n j) := by
  have len : w.length = n := by simpa using perm.length_eq
  have distinct := perm.nodup_iff.mpr (List.nodup_range' (s := 0) (n := n) (step := 1))
  have weights := reverse_inversions w distinct
  rw [len] at weights
  have revPerm := (List.reverse_perm w).trans perm
  constructor
  · intro hw
    obtain ⟨_,h,hwgt⟩ := mem_bucket.mp hw
    exact mem_bucket.mpr ⟨revPerm,(reflection w).mp h, by omega⟩
  · intro hw
    obtain ⟨_,h,hwgt⟩ := mem_bucket.mp hw
    exact mem_bucket.mpr ⟨perm,(reflection w).mpr h, by omega⟩

theorem complementary_counts {D E : List Nat → Prop} (reflection : ∀ w, D w ↔ E w.reverse)
    (n k j : Nat) (total : k+j = triangular n) :
    (bucket D n k).card = (bucket E n j).card := by
  classical
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn List.reverse
    · intro w hw
      exact (reverse_in_buckets reflection total (mem_bucket.mp hw).1).mp hw
    · exact (fun _ _ _ _ e => List.reverse_inj.mp e)
  · apply Finset.card_le_card_of_injOn List.reverse
    · intro w hw
      have perm := (List.reverse_perm w).trans (mem_bucket.mp hw).1
      exact (reverse_in_buckets reflection total perm).mpr (by simpa using hw)
    · exact (fun _ _ _ _ e => List.reverse_inj.mp e)

/-- The same fixed-k comparison holds for any family containing the reversals
of all layered permutations. No closure hypothesis on the family is needed. -/
theorem upper_edge_of_reversed_layered (D : List Nat → Prop)
    (contains : ∀ ds, D (layered 0 ds).reverse) (n k : Nat)
    (large : 1024 ≤ n) (feasible : k ≤ triangular n) (nearMax : 64 * (triangular n - k) ≤ n) :
    2 ^ (n/32) * (bucket D n k).card ≤ (bucket D (n+1) k).card := by
  let E := fun w : List Nat => D w.reverse
  have refl : ∀ w, D w ↔ E w.reverse := by simp [E]
  let j := triangular n - k
  have source : k + j = triangular n := by dsimp [j]; omega
  have target : k + (n+j) = triangular (n+1) := by rw [triangular]; omega
  rw [complementary_counts refl n k j source, complementary_counts refl (n+1) k (n+j) target]
  apply uniform_layered_upper_edge E _ n j large nearMax
  rintro _ ⟨ds,rfl⟩
  exact contains ds

/-- Fixed original inversion count, with an exponential factor uniform in the
stated strip and with an explicit length threshold. -/
theorem cjs_upper_edge (n k : Nat) (large : 1024 ≤ n) (feasible : k ≤ triangular n)
    (nearMax : 64 * (triangular n - k) ≤ n) :
    2 ^ (n / 32) * (bucket Avoid1324 n k).card ≤ (bucket Avoid1324 (n + 1) k).card := by
  apply upper_edge_of_reversed_layered _ _ n k large feasible nearMax
  intro ds
  apply (reverse_avoidance _).mpr
  simpa using layered_avoids_4231 ds 0

end PrincipalInversionMonotonicity
