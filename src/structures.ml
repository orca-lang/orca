module type MONAD =
  sig
    type 'a t
    val bind : 'a t -> ('a -> 'b t) -> 'b t
    val return : 'a -> 'a t
  end

module type STATE =
  sig
     type t
     val empty : t
  end

module type STATE_MONAD =
  functor(State : STATE) ->
  sig
    include MONAD
    val access : 'a t -> 'a
    val put : State.t -> unit t
    val get : State.t t
  end

module StateMonad : STATE_MONAD =
  functor(State : STATE) ->
  struct
    type state = State.t
    type 'a t = state -> ('a * state)

    let bind m f s =
      match m s with
      | (x, s') -> f x s'

    let return a = fun s -> (a, s)

    let access m =
      match m State.empty with
      | (x, s) -> x

    let put s = fun _ -> ((), s)

    let get = fun s -> (s, s)

    let id x = x
  end
