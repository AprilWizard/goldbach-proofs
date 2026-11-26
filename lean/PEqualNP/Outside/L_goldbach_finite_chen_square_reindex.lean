import Mathlib

theorem PEqualNP.Outside.L_goldbach_finite_chen_square_reindex :
    let P := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (Nat.sqrt (n-p)) ∧ (Nat.sqrt (n-p))^2=n-p);
    ∀ (n : ℕ) (v : ℕ → ℝ), (∑ p ∈ P n, v p) = ∑ a ∈ (Finset.Icc 2 (Nat.sqrt n)).filter (fun a => Nat.Prime a ∧ Nat.Prime (n-a^2)), v (n-a^2) := by
  intro P n v
  let t : Finset ℕ := (Finset.Icc 2 (Nat.sqrt n)).filter (fun a => Nat.Prime a ∧ Nat.Prime (n-a^2))
  change (∑ p ∈ P n, v p) = ∑ a ∈ t, v (n-a^2)
  refine Finset.sum_bij (fun p _ => Nat.sqrt (n-p)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hp_range, hp_prime, ha_prime, hsq⟩ := hp
    rw [Finset.mem_range] at hp_range
    have hp_le : p ≤ n := by omega
    have ha_le : Nat.sqrt (n-p) ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (Nat.sub_le _ _)
    have ha_ge : 2 ≤ Nat.sqrt (n-p) := ha_prime.two_le
    have hnp : n - Nat.sqrt (n-p)^2 = p := by omega
    exact ⟨Finset.mem_Icc.mpr ⟨ha_ge, ha_le⟩, ha_prime, by rw [hnp]; exact hp_prime⟩
  · intro p1 hp1 p2 hp2 heq
    rw [Finset.mem_filter, Finset.mem_range] at hp1 hp2
    obtain ⟨hp1r, _, _, hsq1⟩ := hp1
    obtain ⟨hp2r, _, _, hsq2⟩ := hp2
    have hp1le : p1 ≤ n := by omega
    have hp2le : p2 ≤ n := by omega
    have hpow : Nat.sqrt (n-p1)^2 = Nat.sqrt (n-p2)^2 := by rw [heq]
    rw [hsq1, hsq2] at hpow
    omega
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb_ge, hb_le⟩, hb_prime, hnb_prime⟩ := hb
    have hb2_le : b^2 ≤ n := by
      have h1 : b^2 ≤ (Nat.sqrt n)^2 := Nat.pow_le_pow_left hb_le 2
      have h2 : (Nat.sqrt n)^2 < n + 1 := by
        simpa [pow_two] using Nat.sqrt_mul_sqrt_lt_succ n
      omega
    have hsub : n - (n - b^2) = b^2 := Nat.sub_sub_self hb2_le
    refine ⟨n - b^2, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnb_prime, by rw [hsub, Nat.sqrt_eq' b]; exact hb_prime,
        by rw [hsub, Nat.sqrt_eq' b]⟩
    · rw [hsub, Nat.sqrt_eq' b]
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpr, _, _, hsq⟩ := hp
    have hple : p ≤ n := by omega
    have hnp : n - Nat.sqrt (n-p)^2 = p := by omega
    rw [hnp]
