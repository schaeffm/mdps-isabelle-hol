(* Some utility functions. *)

fun id x = x

structure Printf =
   struct
      fun $ (_, f) = f (fn p => p ()) ignore
      fun fprintf out f = f (out, id)
      val printf = fn z => fprintf TextIO.stdOut z
      fun one ((out, f), make) g =
         g (out, fn r =>
            f (fn p =>
               make (fn s =>
                     r (fn () => (p (); TextIO.output (out, s))))))
      fun ` x s = one (x, fn f => f s)
      fun spec to x = one (x, fn f => f o to)
      val B = fn z => spec Bool.toString z
      val I = fn z => spec Int.toString z
      val R = fn z => spec Real.toString z
   end

open Printf


fun println x = print (x ^ "\n")

fun exit_fail msg = (
  println msg;
  OS.Process.exit(OS.Process.failure)
)

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun show_list f d []      = ""
  | show_list f d [x]     = f x
  | show_list f d (x::xs) = f x ^ d ^ show_list f d xs

