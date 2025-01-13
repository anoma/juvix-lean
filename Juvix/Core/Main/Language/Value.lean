
import Juvix.Core.Main.Language.Base

namespace Juvix.Core.Main

inductive Value : Type where
  | unit : Value
  | const : Constant → Value
  | constr_app : (constr : Name) → (args_rev : List Value) → Value
  | closure : (ctx : List Value) → (value : Expr) → Value
  deriving Inhabited

abbrev Context : Type := List Value

end Juvix.Core.Main
