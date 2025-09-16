package sdn

import compiler.SpatialType.BoolV
import compiler.{ASTL, Locus, Ring}

/**
 *
 * @param defined true if value is defined
 * @param value actual partially defined value
 * @tparam L locus
 * @tparam R  ring
 * we very often use partially defined value, defining a class for it allows to regroup all the code for this.
 */
class PartialASTL[L <: Locus, R <: Ring](val defined:BoolV, val value:ASTL[L ,R]){

}

