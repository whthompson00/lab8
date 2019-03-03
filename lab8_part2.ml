(*
                              CS51 Lab 8
                               Functors
                                Part 2
 *)

(* Objective:

This lab practices concepts of functors.
 *)

(*======================================================================
Functors - Part 2.

In this second part of the lab, you'll rewrite the Stack module from
the last lab so that its element type is polymorphic, while adding some
functionality at the same time.

Occasionally, it's useful to be able to take a data structure and
"serialize" it (also called "marshalling"), that is, to transform its
internal computational representation into a format, like a string,
that can be saved in a file or transmitted digitally. It can later be
"deserialized" to recreate the internal representation. You may notice
that this provides an opportunity to break an abstraction barrier:
serializing an object, manipulating its representation, and then
deserializing back to an object could allow for some invariant to be
violated. Even so, serialization has its uses when the circumstances
are warranted. As a result, we'll add to the stack module extremely
basic support for serialization.

In order to do this with an abstract type for an element in a stack,
we also need to have a function "serialize" that can accept an element
and return a string.

We can use a functor to generate a stack that bundles everything
together.

In order to do this, we'll first define a module interface, called
SERIALIZE, that captures the requirements for the elements of a
stack. It requires that a module expose both a data type and a
function that converts values of that type into a string
representation. As you'll see, the SERIALIZE module type is an
appropriate signature for the argument of a functor that generates
stack modules. *)

module type SERIALIZE =
  sig
    type t
    val serialize : t -> string
  end ;;

(* Now we'll define a STACK interface. Notice that unlike the
INT_STACK interface from the previous lab, we'll specify the element
type to be an abstract data type as part of the signature, and add
additional functions for serialization, as well as a couple of
higher-order functions over stacks. *)

module type STACK =
  sig
    exception Empty
    type element
    type stack
    val empty : stack
    val push : element -> stack -> stack
    val top : stack -> element
    val pop : stack -> stack
    val serialize : stack -> string
    val map : (element -> element) -> stack -> stack
    val filter : (element -> bool) -> stack -> stack
    val fold_left : ('a -> element -> 'a) -> 'a -> stack -> 'a
  end ;;

(*......................................................................
Exercise 1A: Rewrite your stack implementation from the last lab to
use the element abstract data type for elements, and also complete the
other functions that the signature requires. We've provided a good
start below.

The serialize function should construct a string in the following
form:

    "N0:N1:N2:...:N"

where N0 was the *first* element pushed onto the stack, N1 was the
*second*, and so on, with N being the *most recent* element pushed to
the stack, that is, the one to be popped next. (This would make
deserialization easier, since elements could be pushed as soon as they
were read.)

(Don't forget that you can implement other functions that are not
specified by the signature if you would like. The module signature
will prevent them from leaking out of the module.)
......................................................................*)

module MakeStack (Element: SERIALIZE) : (STACK with type element = Element.t) =
  struct
    exception Empty

    type element = Element.t

    type stack = element list

    let empty : stack = []

    let push (el : element) (s : stack) : stack =
      el :: s

    let pop_helper (s : stack) : (element * stack) =
      match s with
      | [] -> raise Empty
      | hd :: tl -> (hd, tl)

    let top (s : stack) : element =
      fst (pop_helper s)

    let pop (s : stack) : stack =
      snd (pop_helper s)

    let map (f : element -> element) (s : stack) : stack =
      List.map f s

    let filter : (element -> bool) -> stack -> stack =
      List.filter

    let fold_left : ('a -> element -> 'a) -> 'a -> stack -> 'a =
      List.fold_left

    let serialize (s : stack) : string =
      let f x y = Element.serialize y ^ (if x <> "" then " : " ^ x else "") in
      fold_left f "" s
  end ;;

(*......................................................................
Exercise 1B: Now, make a module "IntStack" by applying the functor
that you just defined to an appropriate module for serializing ints.
......................................................................*)

module IntStack =
  struct
    type t = int
    let serialize = string_of_int
  end ;;

module IntStack : (STACK with type element = IntSerialize.t) =
  MakeStack(IntSerialize) ;;

(*......................................................................
Exercise 1C: Make a module "IntStringStack" that creates a stack whose
elements are int * string pairs. Its serialize function should output
values as strings of the form:

    "(N,'S')"

where N is the int, and S is the string. For instance, a stack with
two elements might be serialized as

    "(1, 'pushed first'):(2, 'pushed second')"     .

For this oversimplified serialization function, you may assume that
the string will be made up of alphanumeric characters only.
......................................................................*)

module IntStringSerialize =
  struct
    type t = (int * string)
    let serialize (n, s) = "(" ^ string_of_int n ^ ",'" ^ s ^ "')"
  end ;;

module IntStringStack =
  MakeStack (IntStringSerialize) ;;
