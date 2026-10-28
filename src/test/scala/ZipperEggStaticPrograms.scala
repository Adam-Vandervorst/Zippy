package morkl

object ZipperEggStaticPrograms:
  def contextMovementProgram: String = ZipperEggContextMovementProgram.program

  def frontierAntimirovProgram: String = ZipperEggFrontierAntimirovProgram.program

  def iterFixpointProgram: String = ZipperEggIterFixpointProgram.program

  def rangeObservationProgram: String = ZipperEggRangeObservationProgram.program

  def descentPrelude(): String = ZipperEggDescentPrelude.program

  def operatorWitnessSection(id: String): String = ZipperEggOperatorWitness.section(id)
