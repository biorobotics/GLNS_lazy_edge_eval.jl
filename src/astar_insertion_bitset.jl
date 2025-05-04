using DataStructures

# VD is visitation DAG
struct VDNode
  parent::Vector{VDNode}
  visited_sets::BitSet
  final_node_idx::Int64
  key::Tuple{BitSet, Int64}
  g_val::Int64
  h_val::Int64
  f_val::Int64
end

function VDNode(parent::Vector{VDNode}, visited_sets::BitSet, final_node_idx::Int64, g_val::Int64, h_val::Int64)
  return VDNode(parent, visited_sets, final_node_idx, (visited_sets, final_node_idx), g_val, h_val, g_val + h_val)
end

struct VDInfo
  before::Vector{BitSet}
  ancestors_per_set::Vector{BitSet}
end

function VDInfo(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64)
  vd_info = VDInfo(Vector{BitSet}(undef, length(membership)), Vector{BitSet}(undef, length(sets)))

  for node_idx=1:length(membership)
    vd_info.before[node_idx] = BitSet()
  end

  for set_idx=1:length(sets)
    vd_info.ancestors_per_set[set_idx] = BitSet()
    for node_idx=1:length(membership)
      if set_idx == membership[node_idx]
        continue
      end
      in_before = true
      for node_idx2 in sets[set_idx]
        if dist[node_idx, node_idx2] != inf_val
          in_before = false
          break
        end
      end
      if in_before
        push!(vd_info.before[node_idx], set_idx)
      end
    end
  end

  return vd_info
end

# function astar_insertion!(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64, stop_time::Float64, vd_info::VDInfo, partial_tour::Vector{Int64}, known_feas_tour::Vector{Int64})
function astar_insertion!(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64, stop_time::Float64, vd_info::VDInfo, partial_tour::Vector{Int64})
  closed_list = Set{Tuple{BitSet, Int64}}()

  open_list = PriorityQueue{VDNode, Int64}()
  root_node = VDNode(Vector{VDNode}(), BitSet(), 1, 0, 0)
  push!(root_node.visited_sets, membership[1])
  enqueue!(open_list, root_node, 0)

  seen_nodes = Dict{Tuple{BitSet, Int64}, VDNode}()
  seen_nodes[root_node.key] = root_node

  # Update ancestors per set
  for set_idx=1:length(sets)
    empty!(vd_info.ancestors_per_set[set_idx])
  end
  visited_nodes_per_set_in_partial_tour = -ones(Int64, length(sets))
  visited_nodes_per_set_in_partial_tour[membership[partial_tour[1]]] = partial_tour[1]
  for tour_idx1 in 2:length(partial_tour)
    node_idx1 = partial_tour[tour_idx1]
    set_idx1 = membership[node_idx1]
    visited_nodes_per_set_in_partial_tour[set_idx1] = node_idx1
    for tour_idx2 in 1:tour_idx1-1
      node_idx2 = partial_tour[tour_idx2]
      set_idx2 = membership[node_idx2]
      push!(vd_info.ancestors_per_set[set_idx1], set_idx2)
    end
  end

  #=
  known_key = (zeros(Bool, length(sets)), 0)
  known_keys = Vector{Tuple{BitSet, Int64}}()
  for node_idx in known_feas_tour
    known_key = (copy(known_key[1]), node_idx)
    known_key[1][membership[node_idx]] = true
    push!(known_keys, known_key)
  end
  =#

  goal_node = VDNode(Vector{VDNode}(), BitSet(), 1, typemax(Int64), 0)
  while length(open_list) != 0 && goal_node.f_val > peek(open_list).first.f_val
    if time() > stop_time
      println("Timeout during A*")
      return Vector{Int64}()
    end

    pop = dequeue!(open_list)
    if pop.key in closed_list
      continue
    end

    push!(closed_list, pop.key)

    neighbors = Vector{Int64}()
    for set_idx=1:length(sets)
      if set_idx in pop.visited_sets
        continue
      end
      if !isempty(setdiff(vd_info.ancestors_per_set[set_idx], pop.visited_sets))
        continue
      end

      this_set = visited_nodes_per_set_in_partial_tour[set_idx] == -1 ? sets[set_idx] : [visited_nodes_per_set_in_partial_tour[set_idx]]
      for node_idx in this_set
        if dist[pop.final_node_idx, node_idx] == inf_val
          continue
        end

        prune = false
        if !isempty(setdiff(vd_info.before[node_idx], pop.visited_sets))
          continue
        end

        push!(neighbors, node_idx)
      end
    end

    #=
    idx = findfirst(==(pop.key), known_keys)
    if idx != nothing && idx != length(known_keys)
      @assert(known_keys[idx + 1][2] in neighbors)
    end
    =#

    for node_idx in neighbors
      neighbor_node = VDNode([pop], copy(pop.visited_sets), node_idx, pop.g_val + dist[pop.final_node_idx, node_idx], 0)
      push!(neighbor_node.visited_sets, membership[node_idx])
      if neighbor_node.key in closed_list
        continue
      end

      if haskey(seen_nodes,  neighbor_node.key) && seen_nodes[neighbor_node.key].g_val <= neighbor_node.g_val
        continue
      end

      seen_nodes[neighbor_node.key] = neighbor_node

      enqueue!(open_list, neighbor_node, neighbor_node.f_val)

      if neighbor_node.f_val < goal_node.f_val && length(neighbor_node.visited_sets) == length(sets)
        goal_node = neighbor_node
      end
    end
  end

  # No solution
  if length(open_list) == 0
    println("No solution found by A*")
    @assert(goal_node.f_val == typemax(Int64))
    return Vector{Int64}()
  end

  tour = [goal_node.final_node_idx]
  node_tmp = goal_node.parent
  while length(node_tmp) != 0
    node = node_tmp[1]
    push!(tour, node.final_node_idx)
    node_tmp = node.parent
  end
  reverse!(tour)

  return tour
end
