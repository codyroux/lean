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
-- local add      = Fun(a, b, nat_rec1(mk_lambda("_", Nat, Nat), b, Fun(n, c, succ(c)), a))




local x = Local('x', Nat)
local y = Local('y', Nat)

function table.reverse ( tab )
    local size = #tab
    local newTable = {}

    for i,v in ipairs ( tab ) do
        newTable[size-i + 1] = v
    end

    return newTable
end

function get_args(expr)
   out = {}
   e = expr
   while e:is_app() do
      table.insert(out, e:arg())
      e = e:fn()
   end
   return table.reverse(out)
end


function mk_pats(vars, eqns)
   local pats = {}
   local rets = {}
   for k, e in pairs(eqns) do
      e_args = get_args(e)
      lhs = e_args[1]
      rhs = e_args[2]

      p_map = {}
      pat_list = get_args(lhs)
      for i, x in pairs(vars) do
         p_map[x] = pat_list[i]
         print(pat_list[i])
      end
      table.insert(pats, p_map)
      table.insert(rets, rhs)
   end
   return pats, rets
end

local empty_tree = {empty = true}
local var_tree = {var = true}
local case_tree = {case = true}

function choose_var(vars, pats)
   if #vars == 0 then
      return nil, empty_tree
   else
      local triv = true
      local v = vars[1]
      for i, ps in pairs(pats) do
         p_v = ps[v]
         if p_v:is_local() then triv = false end
      end
      if triv then
         return v, var_tree
      else
         return v, case_tree
      end
   end
end

function table.copy(t)
   local new = {}
   for i, x in pairs(t) do
      t[i] = x
   end
   return new
end

function abstract(a, b)
end
function instantiate(a, b)

function substitute(e, x, t)
   return instantiate(abstract(e, x), t)
end

function mk_match_tree(name, vars, pats, rets)
   local x, case = choose_var(vars, pats)
   if case.empty then
      if #rets == 1 then
         mk_return(rets[1])
      else
         print("Ambiguous match")
      end
   elseif case.var then
      new = table.copy(vars)
      new[x] = nil
      for i, v in pairs(rets) do
         substitute(v, x, pats[i][x])
      end
   else
      assert(case.case)
   end
end


function fundef(name, vars, eqns)
   local pats, rets = mk_pats(vars, eqns)
   local tree = mk_match_tree(name, vars, pats, rets)
   return fun_from_tree(name, tree)
end

local x = Local("x", Nat)
local y = Local("y", Nat)
local add_cst = Local("add",
                      mk_arrow(Nat, mk_arrow(Nat, Nat)))

-- replace this with the "real" equality
local eq = Local("eq", A)

function Eq(a, b)
   return mk_app(mk_app(eq, a), b)
end

function add(x, y)
   return mk_app(mk_app(add_cst, x), y)
end

function S(x)
   return mk_app(succ, x)
end

add = fundef(add, {x, y},
             {Eq(add(zero, zero)  , zero),
              Eq(add(S(x), zero)  , S(x)),
              Eq(add(zero, S(y))  , S(y)),
              Eq(add(S(x), S(y))  , S(S(add(x,y))))})
