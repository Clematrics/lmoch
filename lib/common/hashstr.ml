module HashedString = struct
  include String

  let equal = String.equal
  let hash = Hashtbl.hash
end

include Hashtbl.Make (HashedString)
