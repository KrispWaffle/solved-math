import SparseCoefficients

namespace PrincipalInversionMonotonicity

def IsLayered (w : List Nat) : Prop := ∃ ds, w = layered 0 ds

theorem layered_append (ds es : List Nat) (s : Nat) :
    layered s (ds ++ es) = layered s ds ++ layered (s + ds.sum) es := by
  induction ds generalizing s with
  | nil => simp [layered]
  | cons d ds ih => simp [layered, ih, Nat.add_assoc]

theorem layered_shift (ds : List Nat) (s t : Nat) :
    (layered s ds).map (t + ·) = layered (t + s) ds := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    simp [layered, List.map_reverse, List.map_add_range', ih, Nat.add_assoc]

theorem layered_closed (u v : List Nat) (hu : IsLayered u) (hv : IsLayered v) :
    IsLayered (directSum u v) := by
  obtain ⟨ds,rfl⟩ := hu
  obtain ⟨es,rfl⟩ := hv
  have len : (layered 0 ds).length = ds.sum := by simpa using (layered_permutation ds 0).length_eq
  exact ⟨ds ++ es, by simp [directSum, len, layered_shift, layered_append]⟩

private theorem binary_library : 2 ≤ (bucket IsLayered 3 1).card := by
  classical
  have first : [0,2,1] ∈ bucket IsLayered 3 1 :=
    mem_bucket.mpr ⟨by decide, ⟨[1,2], rfl⟩, by decide⟩
  have second : [1,0,2] ∈ bucket IsLayered 3 1 :=
    mem_bucket.mpr ⟨by decide, ⟨[2,1], rfl⟩, by decide⟩
  have sub : ({[0,2,1], [1,0,2]} : Finset (List Nat)) ⊆ bucket IsLayered 3 1 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact first
    · exact Finset.mem_singleton.mp h ▸ second
  simpa using Finset.card_le_card sub

theorem library_powers (m : Nat) : 2 ^ m ≤ (bucket IsLayered (3*m) m).card := by
  induction m with
  | zero =>
    exact Finset.card_pos.mpr ⟨[], mem_bucket.mpr ⟨by decide, ⟨[], rfl⟩, rfl⟩⟩
  | succ m ih =>
    have h := (Nat.mul_le_mul ih binary_library).trans
      (coefficient_product_le layered_closed (3*m) 3 m 1)
    simpa [pow_succ, Nat.mul_succ] using h

theorem filler_nonempty (t l : Nat) (room : 3 * (Nat.sqrt (2*t) + 1) ≤ l) :
    1 ≤ (bucket IsLayered l t).card := by
  obtain ⟨ds, _, perm, weight⟩ := exact_inversion_filler t l room
  exact Finset.card_pos.mpr ⟨_, mem_bucket.mpr ⟨perm, ⟨ds,rfl⟩, weight⟩⟩

theorem bucket_mono {D E : List Nat → Prop} (sub : ∀ w, D w → E w) (n j : Nat) :
    (bucket D n j).card ≤ (bucket E n j).card := by
  apply Finset.card_le_card
  intro w hw
  obtain ⟨pw,dw,iw⟩ := mem_bucket.mp hw
  exact mem_bucket.mpr ⟨pw,sub _ dw,iw⟩

/-- Every permutation family containing the layered permutations satisfies
an explicit exponential upper-edge comparison in complementary coordinates. -/
theorem uniform_layered_upper_edge (D : List Nat → Prop)
    (contains : ∀ w, IsLayered w → D w) (n j : Nat)
    (large : 1024 ≤ n) (sparse : 64 * j ≤ n) :
    2 ^ (n/32) * (bucket D n j).card ≤ (bucket D (n+1) (n+j)).card := by
  let m := n / 4
  let l := n + 1 - 3 * m
  let t := n + j - m
  let s := Nat.sqrt (2*t)
  have sl : s * s ≤ 3 * n :=
    (Nat.sqrt_le (2*t)).trans (by dsimp [t,m]; omega)
  have room : 3 * (s + 1) ≤ l := by
    dsimp [l,m]
    by_cases small : s ≤ 64
    · omega
    · have sq := Nat.mul_le_mul_left s (by omega : 39 ≤ s)
      omega
  have lower := (Nat.mul_le_mul (library_powers m) (filler_nonempty t l room)).trans
    (coefficient_product_le layered_closed (3*m) l m t)
  have lengths : 3*m + l = n+1 := by dsimp [l,m]; omega
  have weights : m + t = n+j := by dsimp [t,m]; omega
  rw [Nat.mul_one, lengths, weights] at lower
  have upper := coefficient_le_two_pow D n j (m - n/32) (by dsimp [m]; omega)
  calc
    2 ^ (n / 32) * (bucket D n j).card ≤ 2 ^ (n / 32) * 2 ^ (m - n/32) :=
      Nat.mul_le_mul_left _ upper
    _ = 2 ^ m := by rw [← pow_add]; congr 1; dsimp [m]; omega
    _ ≤ (bucket IsLayered (n+1) (n+j)).card := lower
    _ ≤ (bucket D (n+1) (n+j)).card := bucket_mono contains _ _

end PrincipalInversionMonotonicity
