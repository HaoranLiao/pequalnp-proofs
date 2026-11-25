import Mathlib.Data.List.FinRange
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2215_629
    (grid : let input (x : Fin 25 → Bool) := List.ofFn x ++
        ([1064960,17842176,8912896,25690112,4456448,12845056,393216,1441792,196608,720896,81920,4276224] : List ℕ).map (fun m => (List.finRange 25).any (fun i => m.testBit i.val && x i))
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 29 ∧ C.output < 37+C.size ∧ q < 37+C.size ∧
        ∀ x : Fin 25 → Bool,
          (C.eval (input x) = true ↔ ∃ p l : Fin 25,
            (p.val < 12 ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∈ ([3,4,5,6,9,10] : List ℕ)) ∧ x p = true ∧ x l = true) ∧
          (C.eval (input x) = false → (C.wires (input x)).getD q false = (x 15 || x 21)))
    (attach : let input (x : Fin 25 → Bool) := List.ofFn x ++
        ([1064960,17842176,8912896,25690112,4456448,12845056,393216,1441792,196608,720896,81920,4276224] : List ℕ).map (fun m => (List.finRange 25).any (fun i => m.testBit i.val && x i))
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ), PEqualNP.MetaComplexity.Monotone2 C →
        C.output < 37+C.size → q < 37+C.size →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (r : ℕ),
          PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size+32 ∧ D.output < 25+D.size ∧ r < 25+D.size ∧
          ∀ x : Fin 25 → Bool,
            (D.eval (List.ofFn x) = true ↔ C.eval (input x) = true ∨ ∃ p l : Fin 25,
              (p.val < 12 ∧ 12 ≤ l.val ∧ (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ) ∧ p.val ∉ ([3,4,5,6,9,10] : List ℕ)) ∧ x p = true ∧ x l = true) ∧
            (D.wires (List.ofFn x)).getD r false = ((C.wires (input x)).getD q false || (x 12 || x 13))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C,q,mc,sizeC,outC,flagC,residual⟩ := grid
  obtain ⟨D,r,md,sizeD,outD,flagD,done⟩ := attach C q mc outC flagC
  refine ⟨D,r,md,by omega,outD,flagD,?_⟩
  intro x
  dsimp only
  obtain ⟨valC,auxC⟩ := residual x
  obtain ⟨valD,auxD⟩ := done x
  constructor
  · rw [valD,valC]
    constructor
    · rintro (⟨p,l,⟨hp,hl,hm,_⟩,xp,xl⟩ | ⟨p,l,⟨hp,hl,hm,_⟩,xp,xl⟩)
      all_goals exact ⟨p,l,⟨hp,hl,hm⟩,xp,xl⟩
    · rintro ⟨p,l,⟨hp,hl,hm⟩,xp,xl⟩
      by_cases part : p.val ∈ ([3,4,5,6,9,10] : List ℕ)
      · exact Or.inl ⟨p,l,⟨hp,hl,hm,part⟩,xp,xl⟩
      · exact Or.inr ⟨p,l,⟨hp,hl,hm,part⟩,xp,xl⟩
  · intro off
    rw [auxD,auxC (Bool.eq_false_iff.mpr (fun h => Bool.noConfusion (off.symm.trans (valD.mpr (Or.inl h)))))]
    ac_rfl
