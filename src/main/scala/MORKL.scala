package morkl

import scala.annotation.targetName

enum Path:
  case Symbol(n: String)
  case Variable(n: String)
  case Concat(l: Path, r: Path)

enum Space:
  case Empty
  case Singleton(p: Path)
  case Union(x: Space, y: Space)
  case Intersection(x: Space, y: Space)
  case Subtraction(x: Space, y: Space)
  case Restriction(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Transformation(src: Space, pattern: Path, template: Path)
  case Subspace(src: Space, p: Path)

enum Expr:
  case Read(postfix: Path)
  case Write(postfix: Path, result: Space)

case class Program(s: List[Expr])

object Syntax:
  export Path.*
  export Expr.*
  export Space.*
  import scala.Conversion
//  import scala.language.dynamics
  import scala.language.implicitConversions
  import scala.reflect
  export scala.reflect.Selectable.reflectiveSelectable

//  class PathBuilder(val path: Option[Path]) extends reflect.Selectable:
//    def selectDynamic(name: String): PathBuilder =
//      val addition = if name.startsWith("$") then Variable(name.tail) else Symbol(name)
//      PathBuilder(Some(path.fold(addition)(Concat(_, addition))))
//
//    def applyDynamic(name: String)(args: Any*): Nothing = throw RuntimeException("void")

//  val ^ : PathBuilder = PathBuilder(None)
//
//  given Conversion[PathBuilder, Path] = _.path.get
  object ?
  extension (_q: `?`.type)
    def apply(p: Path): Expr = Read(p)

  extension (p: Path)
    infix def ! (s: Space): Expr = Write(p, s)
  extension (s: Space)
    infix def transform (lhs_rhs: (Path, Space)): Space = Transformation(s, lhs_rhs._1, lhs_rhs._2)

  given Conversion[String, Path] = Symbol.apply
  given Conversion[Path, Space] = Singleton.apply
  extension (arity : Int)
    def apply(xs: Path*): Path = ???

  extension (inline sc: StringContext)
    inline def $(inline args: Any*): Path =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Variable(k): Path

    inline def $: Path =
      val k = StringContext.standardInterpolator(identity, Nil, sc.parts)
      Variable(k): Path


object Examples:
  import Syntax.{*, given}

  val add_index = 2($"family") transform 3("parent", $"x", $"y") -> 3("child", $"y", $"x")

  val parent_query = 2("family", 2("parents", $"people")) ! {
    $"people" transform $"person" -> Subspace(2("family", 3("child")), $"person")
  }

  val mother_query = 2("family", 2("mothers", $"people")) ! {
    $"people" transform $"person" -> Intersection(Subspace(2("family", 3("child")), $"person"), 2("family", 2("female")))
  }

  val sister_query = 2("family", 2("sisters", $"people")) ! {
    $"people" transform $"person" -> {
      Concat($"_", $"siblings") ! Intersection(2("family", 3("child")), Subspace(2("family", 3("parent")), $"person"))
      Intersection($"siblings", 2("family", 2("female")))
    }
  }

  val aunt_query = 2("family", 2("aunts", $"people")) ! {
    $"people" transform $"person" -> {
      $"person_parents" ! Subspace(2("family", 3("child")), $"person")
      Concat($"_1", $"person_grandparents") ! Restriction(2("family", 3("child")), $"person_parents")
      Concat($"_2", $"person_parent_siblings_incl") ! Restriction(2("family", 3("parent")), $"person_grandparents")
      $"person_parent_siblings" ! Subtraction($"person_parent_siblings_incl", $"person_parents")
      Intersection($"person_parent_siblings", 2("family", 2("female")))
    }
  }

  val predecessor = 2("family", 2("predecessors", $"people")) ! {
    $"people" transform $"person" -> {
      $"pred" ! Subspace(2("family", 3("child")), $"person")
      $"oldest" ! $"pred"
      while $"oldest".nonEmpty do // TODO write with recursion
        $"pred" ! Union($"pred", $"oldest")
        Concat($"_", $"oldest") ! Restriction(2("family", 3("child")), $"oldest")
      Composition(Singleton($"person"), $"pred")
    }
  }


@main def example = ()
//  println(Examples.aunt_query)