import NavierStokesAB.SmallData.Lattice

/-!
# Convolutions on `ℓ¹(Λ)`

* `conv_nonneg`: for nonnegative summable `f, g` on `Λ`, the convolution
  `k ↦ ∑ⱼ f j * g (k - j)` is summable with total mass `(∑ f) * (∑ g)`.
* `convCLM K`: for uniformly bounded bilinear symbols `K k j : G →L G →L G`, the bilinear map
  `(b, b') ↦ (k ↦ ∑ⱼ K k j (b j) (b' (k - j)))` on `ℓ¹(Λ, G)`, with norm at most the bound.
-/

open scoped BigOperators

namespace NavierStokesAB.SmallData

/-- The shear `(j, l) ↦ (j + l, j)` on `Λ × Λ`. -/
def shear : Λ × Λ ≃ Λ × Λ where
  toFun p := (p.1 + p.2, p.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv p := by simp
  right_inv q := by simp

theorem conv_nonneg {f g : Λ → ℝ} (hf : Summable f) (hg : Summable g) (hf0 : ∀ k, 0 ≤ f k)
    (hg0 : ∀ k, 0 ≤ g k) :
    (∀ k, Summable fun j => f j * g (k - j)) ∧ Summable (fun k => ∑' j, f j * g (k - j)) ∧
      ∑' k, ∑' j, f j * g (k - j) = (∑' j, f j) * ∑' j, g j := by
  set F : Λ × Λ → ℝ := fun p => f p.2 * g (p.1 - p.2) with hFdef
  have hFe : F ∘ shear = fun p => f p.1 * g p.2 := by
    funext p; simp [F, shear]
  have hprod : Summable fun p : Λ × Λ => f p.1 * g p.2 :=
    Summable.mul_of_nonneg hf hg (fun k => hf0 k) fun k => hg0 k
  have hF : Summable F := by
    rw [← shear.summable_iff, hFe]; exact hprod
  have hF0 : 0 ≤ F := fun p => mul_nonneg (hf0 _) (hg0 _)
  obtain ⟨h1, h2⟩ := (summable_prod_of_nonneg hF0).1 hF
  refine ⟨h1, h2, ?_⟩
  have e1 : ∑' k, ∑' j, f j * g (k - j) = ∑' p, F p := (hF.tsum_prod).symm
  rw [e1, ← shear.tsum_eq F]
  change ∑' p, (F ∘ shear) p = _
  rw [hFe, hf.tsum_mul_tsum hg hprod]

/-! ### `ℓ¹` helpers -/

section L1

variable {G : Type*} [NormedAddCommGroup G]

theorem l1_summable (b : lp (fun _ : Λ => G) 1) : Summable fun k => ‖b k‖ := by
  have := (lp.memℓp b).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  simpa using this

theorem l1_norm_eq (b : lp (fun _ : Λ => G) 1) : ‖b‖ = ∑' k, ‖b k‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
  simp

theorem memℓp_one_of_summable {c : Λ → G} (hc : Summable fun k => ‖c k‖) :
    Memℓp c 1 :=
  memℓp_gen (by simpa using hc)

end L1

/-! ### Bilinear convolution operators -/

section ConvOp

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Uniformly bounded bilinear symbols. -/
structure Symbol (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] where
  K : Λ → Λ → G →L[ℂ] G →L[ℂ] G
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : ∀ k j, ‖K k j‖ ≤ C

variable (S : Symbol G)

theorem Symbol.norm_apply_le (k j : Λ) (x y : G) : ‖S.K k j x y‖ ≤ S.C * (‖x‖ * ‖y‖) := by
  calc ‖S.K k j x y‖ ≤ ‖S.K k j x‖ * ‖y‖ := (S.K k j x).le_opNorm y
    _ ≤ ‖S.K k j‖ * ‖x‖ * ‖y‖ := by gcongr; exact (S.K k j).le_opNorm x
    _ ≤ S.C * ‖x‖ * ‖y‖ := by gcongr; exact S.bound k j
    _ = S.C * (‖x‖ * ‖y‖) := by ring

/-- The pointwise convolution sum. -/
noncomputable def convFun (b b' : lp (fun _ : Λ => G) 1) (k : Λ) : G :=
  ∑' j, S.K k j (b j) (b' (k - j))

theorem conv_bound_summable (b b' : lp (fun _ : Λ => G) 1) :
    (∀ k, Summable fun j => ‖b j‖ * ‖b' (k - j)‖) ∧
      Summable (fun k => ∑' j, ‖b j‖ * ‖b' (k - j)‖) ∧
      ∑' k, ∑' j, ‖b j‖ * ‖b' (k - j)‖ = ‖b‖ * ‖b'‖ := by
  obtain ⟨h1, h2, h3⟩ := conv_nonneg (l1_summable b) (l1_summable b') (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)
  exact ⟨h1, h2, by rw [h3, l1_norm_eq, l1_norm_eq]⟩

theorem convFun_summand_summable (b b' : lp (fun _ : Λ => G) 1) (k : Λ) :
    Summable fun j => ‖S.K k j (b j) (b' (k - j))‖ :=
  (((conv_bound_summable b b').1 k).mul_left S.C).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun j => S.norm_apply_le k j _ _

theorem norm_convFun_le (b b' : lp (fun _ : Λ => G) 1) (k : Λ) :
    ‖convFun S b b' k‖ ≤ S.C * ∑' j, ‖b j‖ * ‖b' (k - j)‖ := by
  unfold convFun
  calc ‖∑' j, S.K k j (b j) (b' (k - j))‖ ≤ ∑' j, ‖S.K k j (b j) (b' (k - j))‖ :=
        norm_tsum_le_tsum_norm (convFun_summand_summable S b b' k)
    _ ≤ ∑' j, S.C * (‖b j‖ * ‖b' (k - j)‖) :=
        Summable.tsum_le_tsum (fun j => S.norm_apply_le k j _ _)
          (convFun_summand_summable S b b' k) (((conv_bound_summable b b').1 k).mul_left S.C)
    _ = S.C * ∑' j, ‖b j‖ * ‖b' (k - j)‖ := tsum_mul_left

theorem convFun_norm_summable (b b' : lp (fun _ : Λ => G) 1) :
    Summable fun k => ‖convFun S b b' k‖ :=
  (((conv_bound_summable b b').2.1).mul_left S.C).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun k => norm_convFun_le S b b' k

theorem tsum_norm_convFun_le (b b' : lp (fun _ : Λ => G) 1) :
    ∑' k, ‖convFun S b b' k‖ ≤ S.C * (‖b‖ * ‖b'‖) := by
  calc ∑' k, ‖convFun S b b' k‖ ≤ ∑' k, S.C * ∑' j, ‖b j‖ * ‖b' (k - j)‖ :=
        Summable.tsum_le_tsum (norm_convFun_le S b b') (convFun_norm_summable S b b')
          ((conv_bound_summable b b').2.1.mul_left S.C)
    _ = S.C * (‖b‖ * ‖b'‖) := by rw [tsum_mul_left, (conv_bound_summable b b').2.2]

/-- The convolution as an element of `ℓ¹`. -/
noncomputable def conv (b b' : lp (fun _ : Λ => G) 1) : lp (fun _ : Λ => G) 1 :=
  ⟨convFun S b b', memℓp_one_of_summable (convFun_norm_summable S b b')⟩

@[simp] theorem conv_apply (b b' : lp (fun _ : Λ => G) 1) (k : Λ) :
    conv S b b' k = ∑' j, S.K k j (b j) (b' (k - j)) := rfl

theorem norm_conv_le (b b' : lp (fun _ : Λ => G) 1) : ‖conv S b b'‖ ≤ S.C * (‖b‖ * ‖b'‖) := by
  rw [l1_norm_eq]; exact tsum_norm_convFun_le S b b'

theorem summable_convSummand (b b' : lp (fun _ : Λ => G) 1) (k : Λ) :
    Summable fun j => S.K k j (b j) (b' (k - j)) :=
  (convFun_summand_summable S b b' k).of_norm

theorem conv_add_left (b₁ b₂ b' : lp (fun _ : Λ => G) 1) :
    conv S (b₁ + b₂) b' = conv S b₁ b' + conv S b₂ b' := by
  ext k
  simp only [conv_apply, lp.coeFn_add, Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  exact (summable_convSummand S b₁ b' k).tsum_add (summable_convSummand S b₂ b' k)

theorem conv_add_right (b b₁ b₂ : lp (fun _ : Λ => G) 1) :
    conv S b (b₁ + b₂) = conv S b b₁ + conv S b b₂ := by
  ext k
  simp only [conv_apply, lp.coeFn_add, Pi.add_apply, map_add]
  exact (summable_convSummand S b b₁ k).tsum_add (summable_convSummand S b b₂ k)

theorem conv_smul_left (c : ℂ) (b b' : lp (fun _ : Λ => G) 1) :
    conv S (c • b) b' = c • conv S b b' := by
  ext k
  simp only [conv_apply, lp.coeFn_smul, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply]
  exact tsum_const_smul'' c

theorem conv_smul_right (c : ℂ) (b b' : lp (fun _ : Λ => G) 1) :
    conv S b (c • b') = c • conv S b b' := by
  ext k
  simp only [conv_apply, lp.coeFn_smul, Pi.smul_apply, map_smul]
  exact tsum_const_smul'' c

/-- The convolution as a bounded bilinear map. -/
noncomputable def convCLM : lp (fun _ : Λ => G) 1 →L[ℂ] lp (fun _ : Λ => G) 1 →L[ℂ]
    lp (fun _ : Λ => G) 1 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (conv S) (conv_add_left S) (conv_smul_left S) (conv_add_right S)
      (conv_smul_right S))
    S.C fun b b' => by simpa [mul_assoc] using norm_conv_le S b b'

@[simp] theorem convCLM_apply (b b' : lp (fun _ : Λ => G) 1) : convCLM S b b' = conv S b b' :=
  rfl

theorem norm_convCLM_le : ‖convCLM S‖ ≤ S.C :=
  LinearMap.mkContinuous₂_norm_le _ S.C_nonneg _

end ConvOp

end NavierStokesAB.SmallData
