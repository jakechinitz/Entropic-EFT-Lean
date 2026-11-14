import Entropic.InversionGluing.Core
import Entropic.InversionGluing.Bridge

/-!
# Inversion gluing of four-port cells

`Core`: cells glued by point inversion through their face centres form the diamond complex; a word
closes exactly when it is balanced; the closed reduced six-words are the three-port hexagons; no ring
of regular mirror-glued cells closes with zero deficit (integer form).

`Bridge`: the complex is the project's diamond graph (`Entropic.DiamondGreen.dNbr`); the half-turn frame
transport `Entropic.AppP.Num.mirror` is unchanged; `inversion_vacuum_compatible` and
`joint_with_effective_model` give one placement satisfying these together with the effective model.

Not proved here: that zero deficit selects the inversion among all gluings, and any relation to the
simplicial host of Appendix J.
-/
