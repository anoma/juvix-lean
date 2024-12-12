
import Juvix.Core.Main.Language

namespace Juvix.Core.Main

def f : Expr -> Expr := λ e =>
  match e with
  | Expr.lambda (body := e) => e
  | _ => Expr.lambda (body := e)

end Juvix.Core.Main
