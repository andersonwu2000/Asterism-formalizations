import ACS12.PressureGlobalFloor

/-! Exact mass rescaling and the source support for the pressure receiver. -/
namespace ACS12

open Set CenteredCircle.AllN

namespace Configuration

noncomputable def scaleMass {n : ℕ} {p : ℝ} (F : Configuration n p) (s : ℝ) (hs : 0 < s) :
    Configuration n p where
  mass i := s * F.mass i
  position := F.position
  center := F.center
  radius := F.radius
  coefficient := s * F.coefficient
  mass_pos i := mul_pos hs (F.mass_pos i)
  radius_pos := F.radius_pos
  distinct := F.distinct
  on_circle := F.on_circle
  centered := by
    simp only [Complex.real_smul,Complex.ofReal_mul,mul_assoc]
    rw [← Finset.mul_sum]
    have h := F.centered
    simp only [Complex.real_smul] at h
    rw [h,mul_zero]
  central i := by
    have hTerm (j : Fin n) : forceTerm p (s * F.mass j) (F.position j - F.position i) =
        s • forceTerm p (F.mass j) (F.position j - F.position i) := by
      simp only [forceTerm,mul_div_assoc,Complex.real_smul,Complex.ofReal_mul,mul_assoc]
    simp only [hTerm,Complex.real_smul]
    rw [← Finset.mul_sum]
    have h := F.central i
    rw [Complex.real_smul] at h
    rw [h]
    push_cast
    ring

theorem scaleMass_regular_iff {n : ℕ} {p : ℝ} (F : Configuration n p) {s : ℝ} (hs : 0 < s) :
    IsEqualMassRegular (F.scaleMass s hs) ↔ IsEqualMassRegular F := by
  constructor
  · rintro ⟨⟨c,hc,hcEq⟩,hRegular⟩
    refine ⟨⟨c / s,div_pos hc hs,?_⟩,hRegular⟩
    intro i
    have h := hcEq i
    change s * F.mass i = c at h
    rw [← h,mul_comm, mul_div_cancel_right₀ _ hs.ne']
  · rintro ⟨⟨c,hc,hcEq⟩,hRegular⟩
    exact ⟨⟨s * c,mul_pos hs hc,fun i => congrArg (s * ·) (hcEq i)⟩,hRegular⟩

end Configuration

namespace Pressure

theorem normalizedPressureSource {n : ℕ} {p : ℝ} (hp : 9 / 5 ≤ p) (hp₂ : p ≤ 2) (hn : 3 ≤ n)
    (F : Configuration n p) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      (∀ i, 1 / 13 < (F.scaleMass s hs).mass i) ∧ (∀ i, (F.scaleMass s hs).mass i ≤ 1) ∧
        (∃ i, (F.scaleMass s hs).mass i = 1) := by
  have hNon : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨i,_,hI⟩ := Finset.exists_max_image Finset.univ F.mass hNon
  have hM := F.mass_pos i
  obtain ⟨C⟩ := F.exists_normalized_chart (by omega)
  refine ⟨(F.mass i)⁻¹,inv_pos.mpr hM,?_,?_,⟨i,inv_mul_cancel₀ hM.ne'⟩⟩
  · intro j
    change (1 / 13 : ℝ) < (F.mass i)⁻¹ * F.mass j
    rw [← div_eq_inv_mul]
    have h := original_mass_floor hn hp hp₂ F C j i
    rw [C.mass_eq,C.mass_eq,div_right_comm] at h
    exact (lt_div_iff₀ hM).mpr (by simpa only [one_div_mul_eq_div] using
      (div_lt_div_iff_of_pos_right (F.mass_pos C.source.root)).mp h)
  · intro j
    change (F.mass i)⁻¹ * F.mass j ≤ 1
    rw [← div_eq_inv_mul]
    exact (div_le_one hM).mpr (hI j (Finset.mem_univ _))

end Pressure
end ACS12
