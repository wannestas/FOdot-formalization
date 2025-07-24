import FodotFormalization.FOdot.Extensional
import FodotFormalization.FOdot.FO

namespace FOsugar
  open Extensional


  abbrev SugarFOSymbolDeclarations (base: SymbolDeclarationExtensions) : SymbolDeclarationExtensions
  := base

  abbrev SugarFOVoc (base : VocabularyExtensions) : VocabularyExtensions :=
  { SymbolDeclarationExtensions := SugarFOSymbolDeclarations base.SymbolDeclarationExtensions
  }

  abbrev SugarFOTerms {baseVoc : VocabularyExtensions} (base: Extensions baseVoc) : TermExtensions (SugarFOVoc baseVoc)
  := base.TermExtensions

  inductive SugarFormulas {vocExts : VocabularyExtensions} (voc : Vocabulary vocExts) (exts: Extensions vocExts) where
  | Or (φ₁ φ₂ : FormulaX voc exts)

  abbrev SugarFOFormulas {baseVoc : VocabularyExtensions} (base: Extensions baseVoc) : FormulaExtensions (SugarFOVoc baseVoc)
  :=  {base.FormulaExtensions with
        XOtherFormula := λ voc => ((SugarFormulas voc base) ⊕ base.FormulaExtensions.XOtherFormula voc)
      }

  abbrev SugarFO {baseVoc : VocabularyExtensions} (base : Extensions baseVoc): Extensions (SugarFOVoc baseVoc) :=
  { TermExtensions := SugarFOTerms base
  , FormulaExtensions := SugarFOFormulas base
  }

end FOsugar
