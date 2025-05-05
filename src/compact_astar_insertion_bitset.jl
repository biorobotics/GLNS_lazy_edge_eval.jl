using DataStructures
using FastPriorityQueues
using StaticBitSets

# VD is visitation DAG
struct VDNode
  tour_idx::Int64
  parent::Vector{VDNode}
  visited_removed_sets::SBitSet{1, UInt32}
  final_node_idx::Int64
  key::Tuple{Int64, SBitSet{1, UInt32}, Int64}
  g_val::Int64
  h_val::Int64
  f_val::Int64
end

function VDNode(tour_idx::Int64, parent::Vector{VDNode}, visited_removed_sets::SBitSet{1, UInt32}, final_node_idx::Int64, g_val::Int64, h_val::Int64)
  return VDNode(tour_idx, parent, visited_removed_sets, final_node_idx, (tour_idx, visited_removed_sets, final_node_idx), g_val, h_val, g_val + h_val)
end

struct VDInfo
  before::Vector{SBitSet{4, UInt32}} # Need to increase the number if we want more targets
  before_time::Float64
  open_pop_time::Float64
  closed_check_time::Float64
  closed_push_time::Float64
  ancestor_check_time::Float64
  inf_and_prune_check_time::Float64
  succ_gen_time::Float64
  succ_closed_time::Float64
  seen_key_time::Float64
  seen_update_time::Float64
  open_push_time::Float64
  goal_check_time::Float64
end

function VDInfo(dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64)
  vd_info = VDInfo(Vector{SBitSet{4, UInt32}}(undef, length(membership)), zeros(12)...)
  if length(sets) == 0
    return vd_info
  end

  # bt = time_ns()

  for node_idx=1:length(membership)
    vd_info.before[node_idx] = SBitSet{4, UInt32}()
  end

  for set_idx=1:length(sets)
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
        vd_info.before[node_idx] = push(vd_info.before[node_idx], set_idx)
      end
    end
  end
  
  # at = time_ns()
  # vd_info.before_time += (at - bt)/1e9

  return vd_info
end

# Note: this whole function assumes open tsp, doesn't account for cost of returning to depot.
# Not a fundamental limitation, I just didn't implement it to handle closed TSP
function astar_insertion!(sets_to_insert::Vector{Int64}, dist::AbstractArray{Int64, 2}, sets::Vector{Vector{Int64}}, membership::Vector{Int64}, inf_val::Int64, stop_time::Float64, vd_info::VDInfo, partial_tour::Vector{Int64}, known_feas_tour::Vector{Int64})
  #=
  # When the next unvisted index in partial_tour is tour_idx, the h value is dist[node_idx, partial_tour[tour_idx]] + h_vals[tour_idx]
  h_vals = Vector{Int64}(undef, length(partial_tour))
  h_vals[length(partial_tour)] = 0
  for tour_idx=length(partial_tour)-1:-1:1
    h_vals[tour_idx] = dist[partial_tour[tour_idx], partial_tour[tour_idx + 1]] + h_vals[tour_idx + 1]
  end
  =#

  closed_list = Set{Tuple{Int64, SBitSet{1,UInt32}, Int64}}()

  # open_list = PriorityQueue{VDNode, Int64}()
  open_list = HeapPriorityQueue{VDNode, Int64}()
  # open_list = SortedVectorPriorityQueue{VDNode, Int64}()
  # open_list = VectorPriorityQueue{VDNode, Int64}()
  # root_node = VDNode(1, Vector{VDNode}(), zeros(Bool, length(sets_to_insert)), 1, 0, dist[1, partial_tour[2]] + h_vals[2])
  root_node = VDNode(1, Vector{VDNode}(), SBitSet{1,UInt32}(), 1, 0, 0)
  enqueue!(open_list, root_node, 0)

  seen_nodes = Dict{Tuple{Int64, SBitSet{1,UInt32}, Int64}, VDNode}()
  seen_nodes[root_node.key] = root_node

  # bt = time_ns()
  
  new_before = Vector{SBitSet{1,UInt32}}(undef, length(membership))
  for node_idx=1:length(membership)
    new_before[node_idx] = SBitSet{1,UInt32}()
    for (removed_set_idx, set_idx) in enumerate(sets_to_insert)
      if set_idx in vd_info.before[node_idx]
        new_before[node_idx] = push(new_before[node_idx], removed_set_idx)
      end
    end
  end

  # at = time_ns()
  # vd_info.before_time += (at - bt)/1e9

  #=
  known_key = (0, SBitSet{1,UInt32}(), 0)
  known_keys = Vector{Tuple{Int64, SBitSet{1,UInt32}, Int64}}()
  for node_idx in known_feas_tour
    next_subset = node_idx in partial_tour ? known_key[2] : push(known_key[2], findfirst(==(membership[node_idx]), sets_to_insert))
    known_key = (known_key[1] + 1, next_subset, node_idx)
    push!(known_keys, known_key)
    println(known_key)
  end
  =#

  # max_tour_idx = 0
  goal_node = VDNode(0, Vector{VDNode}(), SBitSet{1,UInt32}(), 1, typemax(Int64), 0)
  while length(open_list) != 0 && goal_node.f_val > peek(open_list).first.f_val
    if time() >= stop_time
      println("Timeout during A*")
      return Vector{Int64}()
    end

    # bt = time_ns()

    pop = dequeue!(open_list)

    # at = time_ns()
    # vd_info.open_pop_time += (at - bt)/1e9

    # bt = time_ns()
    if pop.key in closed_list
      # at = time_ns()
      # vd_info.closed_check_time += (at - bt)/1e9
      continue
    end

    # at = time_ns()
    # vd_info.closed_check_time += (at - bt)/1e9


    # bt = time_ns()

    push!(closed_list, pop.key)

    # at = time_ns()
    # vd_info.closed_push_time += (at - bt)/1e9

    this_sets = Vector{Int64}()
    this_removed_sets = Vector{Int64}()
    for (removed_set_idx, set_idx) in enumerate(sets_to_insert)
      if removed_set_idx in pop.visited_removed_sets
        continue
      end
      push!(this_sets, set_idx)
      push!(this_removed_sets, removed_set_idx)
    end

    # Handle next non-removed set
    num_nonremoved_visited = pop.tour_idx - length(pop.visited_removed_sets)
    next_nonremoved_idx = num_nonremoved_visited + 1
    if next_nonremoved_idx <= length(partial_tour)
      push!(this_sets, membership[partial_tour[next_nonremoved_idx]])
      push!(this_removed_sets, -1)
    end

    neighbors = Vector{Int64}()
    neighbor_removed_sets = Vector{Int64}()

    for (removed_set_idx, set_idx) in zip(this_removed_sets, this_sets)
      # bt = time_ns()

      this_set = removed_set_idx == -1 ? [partial_tour[next_nonremoved_idx]] : sets[set_idx]
      for node_idx in this_set
        if dist[pop.final_node_idx, node_idx] == inf_val
          continue
        end

        # Check if unvisited removed customer is in BEFORE[node_idx]. If so, prune
        prune = false
        for node_idx2 in new_before[node_idx]
          if !(node_idx2 in pop.visited_removed_sets)
            prune = true
            break
          end
        end
        if prune
          continue
        end

        # Check if unvisited nonremoved node is unreachable from node_idx. If so, prune
        if next_nonremoved_idx <= length(partial_tour) && node_idx != partial_tour[next_nonremoved_idx] && dist[node_idx, partial_tour[next_nonremoved_idx]] == inf_val
          continue
        end

        push!(neighbors, node_idx)
        push!(neighbor_removed_sets, removed_set_idx)
      end

      # at = time_ns()
      # vd_info.inf_and_prune_check_time += (at - bt)/1e9
    end

    # println("pop ", pop.key, " set_idx: ", membership[pop.final_node_idx])
    #=
    idx = findfirst(==(pop.key), known_keys)
    if idx != nothing && idx != length(known_keys)
      if !(known_keys[idx + 1][3] in neighbors)
        node_idx = known_keys[idx + 1][3]

        if dist[pop.final_node_idx, node_idx] == inf_val
          println("inf dist")
        end

        if length(setdiff(new_before[node_idx], pop.visited_removed_sets)) != 0
          println("before")
        end

        # Check if unvisited nonremoved node is unreachable from node_idx. If so, prune
        if next_nonremoved_idx <= length(partial_tour) && node_idx != partial_tour[next_nonremoved_idx] && dist[node_idx, partial_tour[next_nonremoved_idx]] == inf_val
          println("before partial tour")
        end
        throw("Edge in known feas tour not generated during search")
      end
    end
    =#

    for (removed_set_idx, node_idx) in zip(neighbor_removed_sets, neighbors)
      # bt = time_ns()
      # h_val = next_nonremoved_idx > length(partial_tour) ? 0 : dist[node_idx, partial_tour[next_nonremoved_idx]] + h_vals[next_nonremoved_idx]
      h_val = 0
      next_visited_removed_sets = removed_set_idx == -1 ? pop.visited_removed_sets : push(pop.visited_removed_sets, removed_set_idx)
      neighbor_node = VDNode(pop.tour_idx + 1, [pop], next_visited_removed_sets, node_idx, pop.g_val + dist[pop.final_node_idx, node_idx], h_val)
      # at = time_ns()
      # vd_info.succ_gen_time += (at - bt)/1e9
      # bt = time_ns()
      if neighbor_node.key in closed_list
        # at = time_ns()
        # vd_info.succ_closed_time += (at - bt)/1e9
        continue
      end
      # at = time_ns()
      # vd_info.succ_closed_time += (at - bt)/1e9

      # bt = time_ns()
      if haskey(seen_nodes,  neighbor_node.key) && seen_nodes[neighbor_node.key].g_val <= neighbor_node.g_val
        # at = time_ns()
        # vd_info.seen_key_time += (at - bt)/1e9
        continue
      end

      # at = time_ns()
      # vd_info.seen_key_time += (at - bt)/1e9

      # bt = time_ns()

      seen_nodes[neighbor_node.key] = neighbor_node

      # at = time_ns()
      # vd_info.seen_update_time += (at - bt)/1e9

      # bt = time_ns()

      enqueue!(open_list, neighbor_node, neighbor_node.f_val)

      # at = time_ns()
      # vd_info.open_push_time += (at - bt)/1e9

      # bt = time_ns()

      # max_tour_idx = max(max_tour_idx, neighbor_node.tour_idx)
      if neighbor_node.f_val < goal_node.f_val && neighbor_node.tour_idx == length(sets)
        goal_node = neighbor_node
      end

      # at = time_ns()
      # vd_info.goal_check_time += (at - bt)/1e9
    end
  end
  # println("max tour idx: ", max_tour_idx)

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
