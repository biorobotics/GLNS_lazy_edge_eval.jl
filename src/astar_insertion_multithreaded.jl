using DataStructures
using Base.Threads

# VD is visitation DAG
struct VDNode
  parent::Vector{VDNode}
  visited_sets::Vector{Bool}
  final_node_idx::Int64
  key::Tuple{Vector{Bool}, Int64}
  g_val::Int64
  h_val::Int64
  f_val::Int64
end

function VDNode(parent::Vector{VDNode}, visited_sets::Vector{Bool}, final_node_idx::Int64, g_val::Int64, h_val::Int64)
  return VDNode(parent, visited_sets, final_node_idx, (visited_sets, final_node_idx), g_val, h_val, g_val + h_val)
end

struct VDInfo
  before::Array{Bool, 2}
  ancestors_per_set::Array{Bool,2}
end

function VDInfo(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64)
  vd_info = VDInfo(ones(Bool, length(membership), length(sets)), zeros(Bool, length(sets), length(sets)))

  for set_idx=1:length(sets)
    for node_idx=1:length(membership)
      for node_idx2 in sets[set_idx]
        if dist[node_idx, node_idx2] != inf_val
          vd_info.before[node_idx, set_idx] = false
          break
        end
      end
    end
  end

  for node_idx = 2:length(membership)
    vd_info.before[node_idx, membership[node_idx]] = false
  end

  return vd_info
end

# function astar_insertion!(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64, stop_time::Float64, vd_info::VDInfo, partial_tour::Vector{Int64}, known_feas_tour::Vector{Int64})
function astar_insertion!(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64, stop_time::Float64, vd_info::VDInfo, partial_tour::Vector{Int64})
  closed_list = Set{Tuple{Vector{Bool}, Int64}}()

  open_list = PriorityQueue{VDNode, Int64}()
  root_node = VDNode(Vector{VDNode}(), zeros(Bool, length(sets)), 1, 0, 0)
  root_node.visited_sets[membership[1]] = true
  enqueue!(open_list, root_node, 0)

  seen_nodes = Dict{Tuple{Vector{Bool}, Int64}, VDNode}()
  seen_nodes[root_node.key] = root_node

  # Update ancestors per set
  vd_info.ancestors_per_set[:] .= false
  visited_nodes_per_set_in_partial_tour = -ones(Int64, length(sets))
  visited_nodes_per_set_in_partial_tour[membership[partial_tour[1]]] = partial_tour[1]
  for tour_idx1 in 2:length(partial_tour)
    node_idx1 = partial_tour[tour_idx1]
    set_idx1 = membership[node_idx1]
    visited_nodes_per_set_in_partial_tour[set_idx1] = node_idx1
    for tour_idx2 in 1:tour_idx1-1
      node_idx2 = partial_tour[tour_idx2]
      set_idx2 = membership[node_idx2]
      vd_info.ancestors_per_set[set_idx1, set_idx2] = true
    end
    for tour_idx2 in tour_idx1 + 1:length(partial_tour)
      node_idx2 = partial_tour[tour_idx2]
      set_idx2 = membership[node_idx2]
      vd_info.ancestors_per_set[set_idx1, set_idx2] = false
    end
  end

  #=
  known_key = (zeros(Bool, length(sets)), 0)
  known_keys = Vector{Tuple{Vector{Bool}, Int64}}()
  for node_idx in known_feas_tour
    known_key = (copy(known_key[1]), node_idx)
    known_key[1][membership[node_idx]] = true
    push!(known_keys, known_key)
  end
  =#

  goal_node = VDNode(Vector{VDNode}(), zeros(Bool, 1), 1, typemax(Int64), 0)
  while length(open_list) != 0 && goal_node.f_val > peek(open_list).first.f_val
    if time() >= stop_time
      println("Timeout during A*")
      return Vector{Int64}()
    end

    pop = dequeue!(open_list)
    if pop.key in closed_list
      continue
    end

    push!(closed_list, pop.key)

    neighbors_per_thread = Vector{Vector{Int64}}(undef, nthreads())
    for thread_idx=1:nthreads()
      neighbors_per_thread[thread_idx] = Vector{Int64}()
    end

    @threads :static for set_idx=1:length(sets)
      if pop.visited_sets[set_idx]
        continue
      end
      mandatory_ancestor_unvisited = false
      for set_idx2=1:length(sets)
        if vd_info.ancestors_per_set[set_idx, set_idx2] && !pop.visited_sets[set_idx2]
          mandatory_ancestor_unvisited = true
          break
        end
      end
      if mandatory_ancestor_unvisited
        continue
      end

      this_set = visited_nodes_per_set_in_partial_tour[set_idx] == -1 ? sets[set_idx] : [visited_nodes_per_set_in_partial_tour[set_idx]]
      for node_idx in this_set
        if dist[pop.final_node_idx, node_idx] == inf_val
          continue
        end

        prune = false
        for set_idx2=1:length(sets)
          if set_idx2 != membership[node_idx] && vd_info.before[node_idx, set_idx2] && !pop.visited_sets[set_idx2]
            prune = true
            break
          end
        end
        if prune
          continue
        end

        push!(neighbors_per_thread[threadid()], node_idx)
      end
    end
    neighbors = reduce(vcat, neighbors_per_thread)

    #=
    idx = findfirst(==(pop.key), known_keys)
    if idx != nothing && idx != length(known_keys)
      if !(known_keys[idx + 1][2] in neighbors)
        node_idx = known_keys[idx + 1][2]
        set_idx = membership[node_idx]

        mandatory_ancestor_unvisited = false
        for set_idx2=1:length(sets)
          if vd_info.ancestors_per_set[set_idx, set_idx2] && !pop.visited_sets[set_idx2]
            mandatory_ancestor_unvisited = true
            break
          end
        end
        if mandatory_ancestor_unvisited
          println("Mandatory ancestor unvisited")
        end

        this_set = visited_nodes_per_set_in_partial_tour[set_idx] == -1 ? sets[set_idx] : [visited_nodes_per_set_in_partial_tour[set_idx]]
        for node_idx in this_set
          if dist[pop.final_node_idx, node_idx] == inf_val
            println("Inf dist")
          end

          prune = false
          for set_idx2=1:length(sets)
            if set_idx2 != membership[node_idx] && vd_info.before[node_idx, set_idx2] && !pop.visited_sets[set_idx2]
              println("Prune")
              prune = true
              break
            end
          end
        end
        throw("Edge in known feas tour not generated during search")
      end
    end
    =#

    neighbor_nodes_per_thread = Vector{Vector{VDNode}}(undef, nthreads())

    for thread_idx=1:nthreads()
      neighbor_nodes_per_thread[thread_idx] = Vector{VDNode}()
    end

    @threads :static for node_idx in neighbors
      neighbor_node = VDNode([pop], copy(pop.visited_sets), node_idx, pop.g_val + dist[pop.final_node_idx, node_idx], 0)
      neighbor_node.visited_sets[membership[node_idx]] = true
      if neighbor_node.key in closed_list
        continue
      end

      if haskey(seen_nodes,  neighbor_node.key) && seen_nodes[neighbor_node.key].g_val <= neighbor_node.g_val
        continue
      end

      push!(neighbor_nodes_per_thread[threadid()], neighbor_node)
    end

    neighbor_nodes = reduce(vcat, neighbor_nodes_per_thread)

    for neighbor_node in neighbor_nodes
      seen_nodes[neighbor_node.key] = neighbor_node

      enqueue!(open_list, neighbor_node, neighbor_node.f_val)

      if neighbor_node.f_val < goal_node.f_val && all(neighbor_node.visited_sets)
        goal_node = neighbor_node
      end
    end
  end

  # No solution
  if length(open_list) == 0
    println("No solution found by A*")
    if goal_node.f_val != typemax(Int64)
      throw("f_value of goal node should be typemax(Int64)")
    end
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
