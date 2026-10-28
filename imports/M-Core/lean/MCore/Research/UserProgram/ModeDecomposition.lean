import Mathlib
import MCore.Research.UserProgram.I3Geometry

namespace MCore.Research.UserProgram

def ComplexThreeChannel.meanPart (x : ComplexThreeChannel) : ComplexThreeChannel where
  manifesto := x.mean
  travessia := x.mean
  semente := x.mean

def ComplexThreeChannel.oscPart (x : ComplexThreeChannel) : ComplexThreeChannel :=
  x.centered

def ComplexThreeChannel.add (x y : ComplexThreeChannel) : ComplexThreeChannel where
  manifesto := x.manifesto + y.manifesto
  travessia := x.travessia + y.travessia
  semente := x.semente + y.semente

@[ext] theorem ComplexThreeChannel.ext
    {x y : ComplexThreeChannel}
    (hM : x.manifesto = y.manifesto)
    (hT : x.travessia = y.travessia)
    (hS : x.semente = y.semente) : x = y := by
  cases x
  cases y
  simp_all

theorem ComplexThreeChannel.mean_meanPart (x : ComplexThreeChannel) :
    x.meanPart.mean = x.mean := by
  simp [ComplexThreeChannel.meanPart, ComplexThreeChannel.mean]
  ring

theorem ComplexThreeChannel.mean_oscPart (x : ComplexThreeChannel) :
    x.oscPart.mean = 0 := by
  simp [ComplexThreeChannel.oscPart, ComplexThreeChannel.centered,
    ComplexThreeChannel.mean]
  ring

theorem ComplexThreeChannel.meanPart_idempotent (x : ComplexThreeChannel) :
    x.meanPart.meanPart = x.meanPart := by
  apply ComplexThreeChannel.ext <;>
    simp [ComplexThreeChannel.meanPart, ComplexThreeChannel.mean_meanPart]

theorem ComplexThreeChannel.oscPart_idempotent (x : ComplexThreeChannel) :
    x.oscPart.oscPart = x.oscPart := by
  apply ComplexThreeChannel.ext <;>
    simp [ComplexThreeChannel.oscPart, ComplexThreeChannel.centered,
      ComplexThreeChannel.mean_oscPart]

theorem ComplexThreeChannel.meanPart_oscPart (x : ComplexThreeChannel) :
    x.oscPart.meanPart =
      { manifesto := 0, travessia := 0, semente := 0 } := by
  apply ComplexThreeChannel.ext <;>
    simp [ComplexThreeChannel.meanPart, ComplexThreeChannel.mean_oscPart]

theorem ComplexThreeChannel.reconstruct (x : ComplexThreeChannel) :
    x.meanPart.add x.oscPart = x := by
  apply ComplexThreeChannel.ext <;>
    simp [ComplexThreeChannel.add, ComplexThreeChannel.meanPart,
      ComplexThreeChannel.oscPart, ComplexThreeChannel.centered]

end MCore.Research.UserProgram
