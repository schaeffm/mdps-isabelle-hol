(* bag.sml -- an unordered collection, where multiplicity is significant
 * Copyright ©2007 Christopher League <league@contrapunctus.net>
 * 
 * This library is free software; you may redistribute and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; see the file COPYING. 
 *)

signature BAG_SIG =
sig
    type item
    type bag
    val empty : bag
    val singleton : item -> bag
    val count : bag * item -> int
    val add : bag * item -> bag
    val member : bag * item -> bool
    val foldli : (item * int * 'a -> 'a) -> 'a -> bag -> 'a
end

