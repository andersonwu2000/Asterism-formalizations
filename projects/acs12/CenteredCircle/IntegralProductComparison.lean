import CenteredCircle.KernelCalculus

/-!
An unnormalized positive-product comparison. The proof integrates a symmetric
pointwise inequality twice; all four marginal functions are integrable.
-/

namespace CenteredCircle.AllN

open MeasureTheory Filter

theorem integral_four_terms {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h k : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ) (a b c d : ℝ) :
    (∫ x, a * f x + b * g x - c * h x - d * k x ∂μ) =
      a * (∫ x, f x ∂μ) + b * (∫ x, g x ∂μ) -
        c * (∫ x, h x ∂μ) - d * (∫ x, k x ∂μ) := by
  have hab : Integrable (fun x => a * f x + b * g x) μ :=
    (hf.const_mul a).add (hg.const_mul b)
  have habc : Integrable (fun x => a * f x + b * g x - c * h x) μ :=
    hab.sub (hh.const_mul c)
  rw [integral_sub habc (hk.const_mul d), integral_sub hab (hh.const_mul c),
    integral_add (hf.const_mul a) (hg.const_mul b)]
  simp only [integral_const_mul]

theorem integral_product_comparison {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h k : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) (hk : Integrable k μ)
    (hpair : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      0 ≤ f x * g y + f y * g x - h x * k y - h y * k x) :
    (∫ x, h x ∂μ) * (∫ x, k x ∂μ) ≤ (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  have heval (x : α) :
      (∫ y, f x * g y + f y * g x - h x * k y - h y * k x ∂μ) =
      f x * (∫ y, g y ∂μ) + (∫ y, f y ∂μ) * g x -
        h x * (∫ y, k y ∂μ) - (∫ y, h y ∂μ) * k x := by
    simpa only [mul_comm] using integral_four_terms hg hf hk hh (f x) (g x) (h x) (k x)
  have hnonneg : 0 ≤ ∫ x,
      f x * (∫ y, g y ∂μ) + (∫ y, f y ∂μ) * g x -
        h x * (∫ y, k y ∂μ) - (∫ y, h y ∂μ) * k x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hpair] with x hx
    rw [← heval x]
    exact integral_nonneg_of_ae hx
  have heval2 := integral_four_terms hf hg hh hk
    (∫ y, g y ∂μ) (∫ y, f y ∂μ) (∫ y, k y ∂μ) (∫ y, h y ∂μ)
  simp only [mul_comm] at heval2 hnonneg
  rw [heval2] at hnonneg
  nlinarith

end CenteredCircle.AllN
