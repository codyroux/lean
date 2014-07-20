local env      = environment()
local l        = mk_param_univ("l")
local U_l      = mk_sort(l)
local A        = Local("A", U_l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Bool/Prop
local list_l   = Const("list", {l}) -- list.{l}
local Nat      = Const("nat")
local vec_l    = Const("vec", {l})  -- vec.{l}
local zero     = Const("zero")
local succ     = Const("succ")
local forest_l = Const("forest", {l})
local tree_l   = Const("tree",   {l})
local n        = Local("n", Nat)

env = env:add_universe("u")
env = env:add_universe("v")
local u        = global_univ("u")
local v        = global_univ("v")

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

env = add_inductive(env,
                    "nat", Type,
                    "zero", Nat,
                    "succ", mk_arrow(Nat, Nat))
-- In the following inductive datatype, {l} is the list of universe level parameters.
-- 1 is the number of parameters.
-- The Boolean true in {A, U_l, true} is marking that this argument is implicit.
env = add_inductive(env,
                    "list", {l}, 1, Pi(A, U_l1),
                    "nil", Pi(A, list_l(A)),
                    "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))
local nat_rec1 = Const("nat_rec", {1})
local a        = Local("a", Nat)
local b        = Local("b", Nat)
local n        = Local("n", Nat)
local c        = Local("c", Nat)
local add      = Fun(a, b, nat_rec1(mk_lambda("_", Nat, Nat), b, Fun(n, c, succ(c)), a))

-- display_type(env, nat_rec1)
-- display_type(env, add)
local tc = type_checker(env)
assert(tc:is_def_eq(add(succ(succ(zero)), succ(zero)),
                    succ(succ(succ(zero)))))




function iter(f, sexp)
   if sexp:is_nil() then

   elseif sexp:is_cons() then
      local car, cdr = sexp:fields()
      f(car)
      iter(f, cdr)
   else
      f(sexp)
   end
end

function len(sexp)
   local n = 0
   iter(function (a) n = n+1 end,
        sexp)
   return n
end

function map(f, sexp)
   if sexp:is_nil() then
      return sexpr()
   elseif sexp:is_cons() then
      return sexpr(f(sexp:head()), map(f, sexp:tail()))
   else
      return sexpr()
   end
end

function i_th(i, sexp)
   if sexp:is_nil() then
      error("i argument to i_th out of bounds!")
   elseif sexp:is_cons() then
      if i <= 1 then
         return sexp:head()
      else
         return i_th(i-1, sexp:tail())
      end
   else
      if i <=1 then
         return sexp
      else
         error("i arguement to i_th is out of bounds!")
      end
   end
end

pat = sexpr(name('zero'), name('one'), name('two'), name('three'), name('four'))

-- print(len(pat))
-- print(pat)
-- print(map(len, pat))
-- print(i_th(0, pat))
-- print(i_th(1, pat))
-- print(i_th(2, pat))
-- print(i_th(3, pat))
-- print(i_th(4, pat))
-- print(i_th(5, pat))
-- print(i_th(6, pat))

function iter_leaves(f, sexp)
   if sexp:is_nil() then

   elseif sexp:is_cons() then
      local car, cdr = sexp:fields()
      iter_leaves(f, car)
      iter_leaves(f, cdr)
   else
      f(sexp)
   end
end


function get_args(expr)
   out = sexpr(nil)
   e = expr
   while e:is_app() do
      out = sexpr(e:arg(), out)
      e = e:fn()
   end
   return out
end


function get_fun(expr)
   e = expr
   while e:is_app() do
      e = e:fn()
   end
   return e
end

assert(sexpr(a):to_external())

function pat_from_expr(expr)
   args = get_args(expr)
   fun = get_fun(expr)
   args = map(function (a) return a:to_external() end, args)
   return sexpr(fun, args)
end

print(pat_from_expr(add(a, b)))


local x = Local('x', Nat)
local y = Local('y', Nat)
pat = sexpr(add, {x, y},
            sexpr({zero,    zero,    "=", zero},
                  {succ(x), zero,    "=", succ(x)},
                  {zero,    succ(y), "=", succ(y)},
                  {succ(x), succ(y), "=", succ(succ(add(x,y)))}))



function choose_var(vars, pats)
   if #vars == 0  then
      return sexpr("done", nil)
   else
      local i = find_triv(pats)
      if i then
         return sexpr("triv", i)
      else
         return sepxr("split", 1)
      end
   end
end

function build_mt(fun, vars, pats)
   local c = choose_var(vars, pats)
   if c:head() == sexpr("done") then
      if pats:length() ~= 1 then
         error("ambiguous pattern matching")
      else
         return sexpr("return", pats:to_expr())
      end
   elseif c:head() == sexpr("triv") then
      local i = c:tail()
      local x = vars[i]
      table.delete(i, vars)
      old_vars = {}
      iter(function (p)
              table.push(old_vars, p[i])
              table.delete(i, p) end,
           pats)
      return sexpr('var', x, old_vars,
                   build_mt(fun, vars, pats))
   elseif c:head() == sexpr("split") then
      -- get constructor corresponding to the split
      local hd_cstr, subs = pats[1]:fields()
      -- create the variables for the subpatterns
      local sub_vars = mk_sub_vars(cstr)

   else
      error()
   end
end


-- function add_fundef(env, fname, ty, patlen, pats)

-- end

-- m = Const("m")
-- add = Const("add")
-- env = add_fundef(env, "add", mk_arrow(Nat, mk_arrow(Nat, Nat)),
--                  {add(zero, zero), "=", zero,
--                   add(zero, n), "=", n,
--                   add(n, zero), "=", n,
--                   add(succ(n), succ(m)), "=", succ(succ(add(n,m)))})

-- v = Const("v")

-- env = add_fundef(env, "head", Pi({{n, Nat, true}}, mk_arrow(vec_I(Nat, succ(n)), Nat)),
--                  {head(n, cons(m, v)), "=", m})
