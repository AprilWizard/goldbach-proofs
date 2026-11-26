import Mathlib

theorem PEqualNP.Outside.L_goldbach_shift_normalized_support :
    ∀ (n : ℕ) (e η : ℝ) (ω : ℕ → ℝ), 0 < n → 0 < e → 0 < η →
    let W := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0);
    (∑ m ∈ W, ω m) = 1 →
    (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 →
    4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ) := by
  intro n e η ω hn he hη
  dsimp only
  intro hsum hbudget
  let W : Finset ℕ := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0)
  change (∑ m ∈ W, ω m) = 1 at hsum
  change (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 at hbudget
  change 4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ)
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn2 : (0:ℝ) < (n:ℝ)^2 := by positivity
  have hCpos : (0:ℝ) < (n:ℝ)^(2/3+η) := Real.rpow_pos_of_pos hnR _
  have hsplit : (n:ℝ)^(8/3+η) = (n:ℝ)^2 * (n:ℝ)^(2/3+η) := by
    rw [show (8:ℝ)/3 + η = 2 + (2/3 + η) by ring, Real.rpow_add hnR]
    norm_num
  have hcs : (1:ℝ) ≤ (W.card:ℝ) * ∑ m ∈ W, (ω m)^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq W ω (fun _ => (1:ℝ))
    have hs : (∑ m ∈ W, ω m * 1) = 1 := by simpa using hsum
    rw [hs] at h
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have hA : (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η) ≤ e^2/4 := by
    have h := hbudget
    rw [hsplit] at h
    have h2 : ((e/2)*(n:ℝ))^2 = e^2/4 * (n:ℝ)^2 := by ring
    rw [h2] at h
    have h' : ((∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η)) * (n:ℝ)^2 ≤ (e^2/4) * (n:ℝ)^2 := by
      nlinarith only [h]
    exact le_of_mul_le_mul_right h' hn2
  have h3 : (n:ℝ)^(2/3+η) ≤ (W.card:ℝ) * ((∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η)) := by
    calc (n:ℝ)^(2/3+η) = 1 * (n:ℝ)^(2/3+η) := by ring
      _ ≤ ((W.card:ℝ) * ∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η) :=
        mul_le_mul_of_nonneg_right hcs hCpos.le
      _ = (W.card:ℝ) * ((∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η)) := by ring
  calc 4*(n:ℝ)^(2/3+η) ≤ 4*((W.card:ℝ) * ((∑ m ∈ W, (ω m)^2) * (n:ℝ)^(2/3+η))) := by
        nlinarith only [h3]
    _ ≤ 4*((W.card:ℝ) * (e^2/4)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)
        · norm_num
    _ = e^2*(W.card:ℝ) := by ring