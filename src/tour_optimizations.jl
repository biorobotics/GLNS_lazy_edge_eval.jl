# Copyright 2017 Stephen L. Smith and Frank Imeson
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

using DataStructures

mutable struct AStarNode
  seq_idx::Int64
  node_idx::Int64
  g::Int64
  h::Int64
  f::Int64
  back::Int64
end

function AStarNode(seq_idx, node_idx, g, h, back)
  return AStarNode(seq_idx, node_idx, g, h, g + h, back)
end

function AStarNode(seq_idx, node_idx, g, back)
  return AStarNode(seq_idx, node_idx, g, 0, g, back)
end


"""
Sequentially moves each vertex to its best point on the tour.
Repeats until no more moves can be found
"""
function moveopt!(tour::Array{Int64, 1}, dist::AbstractArray{Int64,2}, sets::Vector{Vector{Int64}}, 
				  member::Array{Int64,1}, setdist::Distsv)
    improvement_found = true
    number_of_moves = 0
    start_position = 1

    @inbounds while improvement_found && number_of_moves < 10
        improvement_found = false
        for i = start_position:length(tour)
            select_vertex = tour[i]
            delete_cost = removal_cost(tour, dist, i)
			set_ind = member[select_vertex]
            splice!(tour, i)  # remove vertex from tour

            # find the best place to insert the vertex
            v, pos, cost = insert_cost_lb(tour, dist, sets[set_ind], set_ind, setdist, 
										  select_vertex, i, delete_cost)
            insert!(tour, pos, v)
            # check if we found a better position for vertex i
            if cost < delete_cost
                improvement_found = true
                number_of_moves += 1
                start_position = min(pos, i) # start looking for swaps where tour change began
                break
            end
        end
    end
end


function moveopt_rand!(tour::Array{Int64, 1}, dist::AbstractArray{Int64,2}, sets::Vector{Vector{Int64}}, 
				  member::Array{Int64,1}, iters::Int, setdist::Distsv)
	tour_inds = collect(1:length(tour))
	@inbounds for i = 1:iters # i = rand(1:length(tour), iters)
		i = incremental_shuffle!(tour_inds, i)
		select_vertex = tour[i]
		
		# first check if this vertex should be moved
		delete_cost = removal_cost(tour, dist, i)
	    set_ind = member[select_vertex]
		splice!(tour, i)  # remove vertex from tour
	    v, pos, cost = insert_cost_lb(tour, dist, sets[set_ind], set_ind, setdist, 
								      select_vertex, i, delete_cost)
		insert!(tour, pos, v)
    end
end


"""
compute the cost of inserting vertex v into position i of tour
"""
@inline function insert_cost_lb(tour::Array{Int64,1}, dist::AbstractArray{Int64,2}, set::Array{Int64, 1}, setind::Int, 
						   setdist::Distsv, bestv::Int, bestpos::Int, best_cost::Int)
    @inbounds for i = 1:length(tour)
		v1 = prev_tour(tour, i) # first check lower bound
		lb = setdist.vert_set[v1, setind] + setdist.set_vert[setind, tour[i]] - dist[v1, tour[i]]
		lb > best_cost && continue

		for v in set
	        insert_cost = dist[v1, v] + dist[v, tour[i]] - dist[v1, tour[i]]
	        if insert_cost < best_cost
				best_cost = insert_cost
				bestv = v
				bestpos = i
	        end
		end
    end
    return bestv, bestpos, best_cost
end

@inline function insert_cost_lb_constrained(tour::Array{Int64,1}, dist, set::Array{Int64, 1}, setind::Int, 
						   setdist::Distsv, bestv::Int, bestpos::Int, best_cost::Int, inf_val::Int64, member::Vector{Int64}, sets, best_repaired_node_seq::Vector{Int64})
    @inbounds for i = 1:length(tour)
		v1 = prev_tour(tour, i) # first check lower bound
		lb = setdist.vert_set[v1, setind] + setdist.set_vert[setind, tour[i]] - dist[v1, tour[i]]
		lb > best_cost && setdist.set_vert[setind, tour[i]] != inf_val && continue
		for v in set
        insert_cost = typemax(Int64)
        repaired_node_seq = Vector{Int64}()
        if dist[v1, v] != inf_val && dist[v, tour[i]] == inf_val
          seen_nodes = Dict{Int64,AStarNode}()
          seen_nodes[v] = AStarNode(i - 1, v, 0, -1)
          open_list = PriorityQueue{AStarNode, Int64}()
          enqueue!(open_list, seen_nodes[v], 0)
          closed_list = Set{Int64}()
          goal_f = typemax(Int64)
          goal_node_idx = -1
          while length(open_list) != 0
            if goal_f <= peek(open_list)[1].f
              break
            end
            pop = dequeue!(open_list)
            if pop.node_idx in closed_list
              # Outdated copy of node. Must have worse or equal g-value to the one in seen_nodes,
              # because of consistent heuristic (always equals 0)
              @assert(pop.g >= seen_nodes[pop.node_idx].g)
              continue
            end
            push!(closed_list, pop.node_idx)
            next_seq_idx = pop.seq_idx%length(tour) + 1
            next_set_idx = member[tour[next_seq_idx]]
            next_set = sets[next_set_idx]
            if next_set_idx == member[v1]
              next_set = [v1]
            end
            for next_node_idx in next_set
              if dist[pop.node_idx, next_node_idx] != inf_val &&
                 !(next_node_idx in closed_list) &&
                 (!haskey(seen_nodes, next_node_idx) || pop.g + dist[pop.node_idx, next_node_idx] < seen_nodes[next_node_idx].g)
                seen_nodes[next_node_idx] = AStarNode(next_seq_idx, next_node_idx, pop.g + dist[pop.node_idx, next_node_idx], pop.node_idx)
                enqueue!(open_list, seen_nodes[next_node_idx], seen_nodes[next_node_idx].f)
                if next_node_idx == tour[next_seq_idx] && seen_nodes[next_node_idx].f < goal_f
                  goal_f = seen_nodes[next_node_idx].f
                  goal_node_idx = next_node_idx
                end
              end
            end
          end

          if goal_f != typemax(Int64)
            repaired_node_seq = [goal_node_idx]
            node = seen_nodes[goal_node_idx]
            while node.back != -1
              node = seen_nodes[node.back]
              push!(repaired_node_seq, node.node_idx)
            end
            reverse!(repaired_node_seq)
            @assert(repaired_node_seq[1] == v)
            insert_cost = dist[v1, v]
            zero_based_i = (i - 1)%length(tour)
            for zero_based_repaired_seq_idx=0:length(repaired_node_seq) - 2
              zero_based_tour_idx = (zero_based_i - 1 + zero_based_repaired_seq_idx)%length(tour)
              zero_based_next_tour_idx = (zero_based_tour_idx + 1)%length(tour)
              repaired_seq_idx = zero_based_repaired_seq_idx + 1
              insert_cost += dist[repaired_node_seq[repaired_seq_idx], repaired_node_seq[repaired_seq_idx + 1]] - dist[zero_based_tour_idx + 1, zero_based_next_tour_idx + 1]
            end
          else
            continue
          end
        else
          insert_cost = dist[v1, v] + dist[v, tour[i]] - dist[v1, tour[i]]
        end
        if insert_cost < best_cost
          best_cost = insert_cost
          bestv = v
          bestpos = i
          best_repaired_node_seq = repaired_node_seq
        end
		end
    end
    return bestv, bestpos, best_cost, best_repaired_node_seq
end


"""
determine the cost of removing the vertex at position i in the tour
"""
@inline function removal_cost(tour::Array{Int64, 1}, dist::AbstractArray{Int64,2}, i::Int64)
    if i == 1
        return dist[tour[end], tour[i]] + dist[tour[i], tour[i+1]] - dist[tour[end], tour[i+1]]
    elseif i == length(tour)
        return dist[tour[i-1], tour[i]] + dist[tour[i], tour[1]] - dist[tour[i-1], tour[1]]
    else
        return dist[tour[i-1], tour[i]] + dist[tour[i], tour[i+1]] - dist[tour[i-1], tour[i+1]]
	end
end


""" repeatedly perform moveopt and reopt_tour until there is no improvement """
function opt_cycle!(current::Tour, dist::AbstractArray{Int64,2}, sets::Vector{Vector{Int64}}, 
					member::Array{Int64,1}, param::Dict{Symbol, Any}, setdist::Distsv, use)
	current.cost = tour_cost(current.tour, dist)
	prev_cost = current.cost
	for i=1:5
		if i % 2 == 1
			current.tour = reopt_tour(current.tour, dist, sets, member, param)
		elseif param[:mode] == "fast" || use == "partial"
			moveopt_rand!(current.tour, dist, sets, member, param[:max_removals], setdist)
		else
			moveopt!(current.tour, dist, sets, member, setdist)
		end
		current.cost = tour_cost(current.tour, dist)
		if i > 1 && (current.cost >= prev_cost || use == "partial")
			return
		end
		prev_cost = current.cost
	end	
end


"""
Given an ordering of the sets, this alg performs BFS to find the 
optimal vertex in each set
"""
function reopt_tour(tour::Array{Int64,1}, dist::AbstractArray{Int64,2}, sets::Vector{Vector{Int64}}, 
					member::Array{Int64,1}, param::Dict{Symbol, Any})
    best_tour_cost = tour_cost(tour, dist)
	new_tour = copy(tour)
	min_index = min_setv(tour, sets, member, param)	
    tour = [tour[min_index:end]; tour[1:min_index-1]]

    prev = zeros(Int64, param[:num_vertices])   # initialize cost_to_come
    cost_to_come = zeros(Int64, param[:num_vertices])
    @inbounds for start_vertex in sets[member[tour[1]]]
 		relax_in!(cost_to_come, dist, prev, Int64[start_vertex], sets[member[tour[2]]])
        for i = 3:length(tour)  # cost to get to ith set on path through (i-1)th set
            relax_in!(cost_to_come, dist, prev, sets[member[tour[i-1]]], sets[member[tour[i]]])
        end
        # find the cost back to the start vertex.
        tour_cost, start_prev = relax(cost_to_come, dist, sets[member[tour[end]]], start_vertex)
        if tour_cost < best_tour_cost   # reconstruct the path
			best_tour_cost = tour_cost
            new_tour = extract_tour(prev, start_vertex, start_prev)
        end
    end
	return new_tour
end


""" Find the set with the smallest number of vertices """
function min_setv(tour::Array{Int64, 1}, sets::Vector{Vector{Int64}}, member::Array{Int64, 1}, 
				  param::Dict{Symbol, Any})
	min_set = param[:min_set]
	@inbounds for i = 1:length(tour)
		member[tour[i]] == min_set && return i
	end
	return 1
end


"""
extracting a tour from the prev pointers.
"""
function extract_tour(prev::Array{Int64,1}, start_vertex::Int64, start_prev::Int64)
    tour = [start_vertex]
    vertex_step = start_prev
    while prev[vertex_step] != 0
        push!(tour, vertex_step)
        vertex_step = prev[vertex_step]
    end
    return reverse(tour)
end


"""
outputs the new cost and prev for vertex v2 after relaxing
does not actually update the cost
"""
@inline function relax(cost::Array{Int64, 1}, dist::AbstractArray{Int64,2}, set1::Array{Int64, 1}, v2::Int64)
	v1 = set1[1]
	min_cost = cost[v1] + dist[v1, v2]
	min_prev = v1
    @inbounds for i = 2:length(set1)
		v1 = set1[i]
		newcost = cost[v1] + dist[v1, v2]
        if min_cost > newcost
            min_cost, min_prev = newcost, v1
        end
    end
    return min_cost, min_prev
end


"""
relaxes the cost of each vertex in the set set2 in-place.
"""
@inline function relax_in!(cost::Array{Int64, 1}, dist::AbstractArray{Int64,2}, prev::Array{Int64, 1}, 
				 set1::Array{Int64, 1}, set2::Array{Int64, 1})
	@inbounds for v2 in set2
		v1 = set1[1]
		cost[v2] = cost[v1] + dist[v1, v2]
		prev[v2] = v1
        for i = 2:length(set1)
			v1 = set1[i]
			newcost = cost[v1] + dist[v1, v2]
            if cost[v2] > newcost
				cost[v2], prev[v2] = newcost, v1
            end
        end
    end
end
