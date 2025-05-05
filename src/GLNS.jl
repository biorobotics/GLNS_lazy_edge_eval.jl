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
module GLNS
export solver
using Random
using Sockets
using Printf
using NPZ
using CPUTime
using ThreadPinning
using Base.Threads
# include("astar_insertion.jl")
include("compact_astar_insertion.jl")
include("utilities.jl")
include("parse_print.jl")
include("tour_optimizations.jl")
include("adaptive_powers.jl")
include("insertion_deletion.jl")
include("parameter_defaults.jl")

function floyd_warshall!(dist, inf_val)
  num_nodes = size(dist, 1)
  # Can't use node 1 as pivot because it corresponds to traveling back in time
  @inbounds for pivot in 2:num_nodes
    # Relax dist[u, v] = min(dist[u, v], dist[u, pivot]+dist[pivot, v]) for all u, v
    for v in 1:num_nodes
      d = dist[pivot, v]
      d == inf_val && continue
      for u in 1:num_nodes
        ans = (dist[u, pivot] == inf_val ? inf_val : dist[u, pivot] + d)
        if dist[u, v] > ans
          dist[u, v] = ans
        end
      end
    end
  end
end

"""
Main GTSP solver, which takes as input a problem instance and
some optional arguments
"""
function solver(problem_instance::String, client_socket::TCPSocket, given_initial_tours::AbstractArray{Int64,1}, start_time_for_tour_history::UInt64, inf_val::Int64, evaluated_edges::Vector{Tuple{Int64, Int64}}, open_tsp::Bool, num_vertices::Int64, num_sets::Int64, sets::Vector{Vector{Int64}}, dist::AbstractArray{Int64,2}, membership::Vector{Int64}, instance_read_time::Float64, cost_mat_read_time::Float64, run_perf::Bool=false, perf_file::String="", powers::Dict{String,Any}=Dict{String,Any}(), seed_rng::Bool=true; args...)
  # println("This is a fork of GLNS allowing for lazy edge evaluation")
  if seed_rng
    Random.seed!(1234)
  end

  # floyd_warshall!(dist, inf_val)

	param = parameter_settings(num_vertices, num_sets, sets, problem_instance, args)
  if length(given_initial_tours) != 0
    @assert(length(given_initial_tours)%num_sets == 0)
    param[:cold_trials] = div(length(given_initial_tours), num_sets)
  end
	#####################################################
	init_time = time()

  if param[:lazy_edge_eval] == 1
    confirmed_dist = zeros(Bool, size(dist, 1), size(dist, 2))
    for edge in evaluated_edges
      confirmed_dist[edge[1], edge[2]] = true
    end
    confirmed_dist[dist .== inf_val] .= true
    if open_tsp
      confirmed_dist[1:end, 1] .= true
    end
  else
    confirmed_dist = zeros(Bool, 1, 1)
  end

	count = Dict(:latest_improvement => 1,
	  			 :first_improvement => false,
	 		     :warm_trial => 0,
	  		     :cold_trial => 1,
				 :total_iter => 0,
				 :print_time => init_time)
	lowest = Tour(Int64[], typemax(Int64))

  # Perf code
  perf_pid = -1
  if run_perf && occursin("custom0", problem_instance)
    @assert(length(perf_file) != 0)
    pid = string(getpid())
    # timestr = string(time())
    # Assumes we're just storing in the local directory so there aren't any slashes in the output file name. Also assumes perf_data has been created
    num = 0
    # cmd = `perf stat -p $pid -M tma_dram_bound,tma_l1_bound,tma_l2_bound,tma_l3_bound -e cache-references,cache-misses,L1-dcache-load-misses,L1-dcache-loads,L1-dcache-stores,L1-icache-load-misses,l2_rqsts.miss,l2_rqsts.references,LLC-loads,LLC-load-misses,LLC-stores,LLC-store-misses -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_dram_bound,tma_l1_bound,tma_l2_bound,tma_l3_bound -e cache-references,cache-misses,L1-dcache-load-misses,L1-dcache-loads,L1-dcache-stores,L1-icache-load-misses,l2_rqsts.miss,l2_rqsts.references,LLC-loads,LLC-load-misses,LLC-stores,LLC-store-misses,offcore_response.pf_l1d_and_sw.l3_hit.any_snoop -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_dram_bound,tma_l1_bound,tma_l2_bound,tma_l3_bound -e L1-dcache-load-misses,L1-dcache-loads,l2_rqsts.all_demand_data_rd,l2_rqsts.demand_data_rd_miss,LLC-loads,LLC-load-misses -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_l1_bound -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_dram_bound,tma_l1_bound,tma_l2_bound,tma_l3_bound -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_l1_bound -e L1-dcache-load-misses,L1-dcache-loads -o $perf_file`
    # cmd = `perf stat -p $pid -e L1-dcache-load-misses,L1-dcache-loads,offcore_response.pf_l1d_and_sw.l3_hit.any_snoop,offcore_response.pf_l1d_and_sw.l3_miss.any_snoop -o $perf_file`
    cmd = `perf stat -p $pid -M tma_l1_bound,tma_l2_bound,tma_l3_bound,tma_dram_bound -e LLC-loads,LLC-load-misses -o $perf_file`
    # cmd = `perf stat -p $pid -M tma_dram_bound -o $perf_file`
    perf_proc = run(pipeline(cmd, stdout=stdout, stderr=stdout); wait=false)
    perf_pid = getpid(perf_proc)
    # sleep(1)
  end

	start_time = time_ns()
  start_proc_time = CPUtime_us()
	# compute set distances which will be helpful
	setdist = set_vertex_dist(dist, num_sets, membership)

  if length(powers) == 0
    powers = initialize_powers(param)
  else
    power_update!(powers, param)
  end

  tour_history = Array{Tuple{Float64, Array{Int64,1}, Int64},1}()
  num_trials_feasible = 0
  num_trials = 0

  stop_upon_budget = param[:budget] != typemin(Int64)

  do_astar_insertion = true
  if do_astar_insertion
    vd_info = VDInfo(dist, sets, membership, inf_val)
  else
    vd_info = VDInfo(zeros(Int64, 1, 1), Vector{Vector{Int64}}(), zeros(Int64, 1), inf_val)
  end

  #=
  tour = astar_insertion!(collect(2:length(sets)), dist, sets, membership, inf_val, init_time + param[:max_time], vd_info, [1], [1])
  cost = tour_cost(tour, dist)
  println(time() - init_time)
  println(tour)
  println(cost)
  @assert(false)
  =#

	while true
    if count[:cold_trial] > param[:cold_trials] && !stop_upon_budget
      break
    end
		# build tour from scratch on a cold restart
    if length(given_initial_tours) != 0
      start_idx = (count[:cold_trial] - 1)*num_sets + 1
      end_idx = count[:cold_trial]*num_sets
      initial_tour = given_initial_tours[start_idx:end_idx]
    else
      initial_tour = Vector{Int64}()
    end
    best = initial_tour!(lowest, dist, sets, setdist, count[:cold_trial], param, confirmed_dist, client_socket, num_sets, membership, initial_tour)
    timer = (time_ns() - start_time)/1.0e9
		# print_cold_trial(count, param, best)
		phase = :early

    if count[:cold_trial] > 1
      power_update!(powers, param)
    end

		while count[:warm_trial] <= param[:warm_trials]
			iter_count = 1
			current = Tour(copy(best.tour), best.cost)
			temperature = 1.442 * param[:accept_percentage] * best.cost
			# accept a solution with 50% higher cost with 0.05% change after num_iterations.
			cooling_rate = ((0.0005 * lowest.cost)/(param[:accept_percentage] *
									current.cost))^(1/param[:num_iterations])

			if count[:warm_trial] > 0	  # if warm restart, then use lower temperature
        temperature *= cooling_rate^(param[:num_iterations]/2)
				phase = :late
			end
			while count[:latest_improvement] <= (count[:first_improvement] ?
                                           param[:latest_improvement] : param[:first_improvement])

				if iter_count > param[:num_iterations]/2 && phase == :early
					phase = :mid  # move to mid phase after half iterations
				end
        if do_astar_insertion
          trial = remove_insert_astar(current, best, dist, membership, setdist, sets, powers, param, phase, inf_val, init_time + param[:max_time], vd_info)
        else
          trial = remove_insert(current, best, dist, membership, setdist, sets, powers, param, phase)
        end

				if trial.cost < best.cost
          if param[:lazy_edge_eval] == 1
            eval_edges!(trial, dist, confirmed_dist, client_socket, setdist, num_sets, membership)
          end
		    end

        trial_infeasible = dist[trial.tour[end], trial.tour[1]] == inf_val
        @inbounds for i in 1:length(trial.tour)-1
          if trial_infeasible
            break
          end
          trial_infeasible = dist[trial.tour[i], trial.tour[i+1]] == inf_val
        end
        if ~trial_infeasible
          num_trials_feasible += 1
        end
        num_trials += 1

        # decide whether or not to accept trial
				if accepttrial_noparam(trial.cost, current.cost, param[:prob_accept]) ||
				   accepttrial(trial.cost, current.cost, temperature)
					param[:mode] == "slow" && opt_cycle!(trial, dist, sets, membership, param, setdist, "full")
				  current = trial
		    end

		    if current.cost < best.cost
					count[:latest_improvement] = 1
					count[:first_improvement] = true
					if count[:cold_trial] > 1 && count[:warm_trial] > 1
						count[:warm_trial] = 1
					end
					best = current
          prev_best_cost = best.cost
          prev_best_tour = best.tour
          opt_cycle!(best, dist, sets, membership, param, setdist, "full")
          if param[:lazy_edge_eval] == 1
            eval_edges!(best, dist, confirmed_dist, client_socket, setdist, num_sets, membership)
            if best.cost > prev_best_cost
              best.cost = prev_best_cost
              best.tour = prev_best_tour
            end
          end
	      else
					count[:latest_improvement] += 1
				end

				# if we've come in under budget, or we're out of time, then exit
			  if best.cost <= param[:budget] || time() - init_time > param[:max_time]
					param[:timeout] = (time() - init_time > param[:max_time])
					param[:budget_met] = best.cost <= param[:budget]
					timer = (time_ns() - start_time)/1.0e9
					lowest.cost > best.cost && (lowest = best)
          if param[:output_file] != "None"
            push!(tour_history, (round((time_ns() - start_time_for_tour_history)/1.0e9, digits=3), lowest.tour, lowest.cost))
          end

          if run_perf && occursin("custom0", problem_instance)
            @assert(perf_pid != -1)
            run(`kill -2 $perf_pid`)
          end

					print_best(count, param, best, lowest, init_time)
          proc_timer = (CPUtime_us() - start_proc_time)/1e6
					print_summary(lowest, timer, proc_timer, membership, param, tour_history, cost_mat_read_time, instance_read_time, num_trials_feasible, num_trials, true)
          return powers
				end

		    temperature *= cooling_rate  # cool the temperature
				iter_count += 1
				count[:total_iter] += 1

        if (length(tour_history) == 0 || (best.cost < tour_history[end][3])) && param[:output_file] != "None"
          timer = (time_ns() - start_time)/1.0e9
          push!(tour_history, (round((time_ns() - start_time_for_tour_history)/1.0e9, digits=3), best.tour, best.cost))
          # println("Printing tour history")
          # println(tour_history)
        end

				print_best(count, param, best, lowest, init_time)
			end
			print_warm_trial(count, param, best, iter_count)
			# on the first cold trial, we are just determining
			count[:warm_trial] += 1
			count[:latest_improvement] = 1
			count[:first_improvement] = false

      # if we've come in under budget, or we're out of time, then exit
      if best.cost <= param[:budget] || time() - init_time > param[:max_time]
        param[:timeout] = (time() - init_time > param[:max_time])
        param[:budget_met] = best.cost <= param[:budget]
        timer = (time_ns() - start_time)/1.0e9
        lowest.cost > best.cost && (lowest = best)
        if param[:output_file] != "None"
          push!(tour_history, (round((time_ns() - start_time_for_tour_history)/1.0e9, digits=3), lowest.tour, lowest.cost))
        end

        if run_perf && occursin("custom0", problem_instance)
          @assert(perf_pid != -1)
          run(`kill -2 $perf_pid`)
        end

        print_best(count, param, best, lowest, init_time)
        proc_timer = (CPUtime_us() - start_proc_time)/1e6
        print_summary(lowest, timer, proc_timer, membership, param, tour_history, cost_mat_read_time, instance_read_time, num_trials_feasible, num_trials, true)
        return powers
      end
		end
		lowest.cost > best.cost && (lowest = best)
		count[:warm_trial] = 0
		count[:cold_trial] += 1

		# print_powers(powers)

	end
	timer = (time_ns() - start_time)/1.0e9
  if param[:output_file] != "None"
    push!(tour_history, (round((time_ns() - start_time_for_tour_history)/1.0e9, digits=3), lowest.tour, lowest.cost))
  end

  if run_perf && occursin("custom0", problem_instance)
    @assert(perf_pid != -1)
    run(`kill -2 $perf_pid`)
  end
  proc_timer = (CPUtime_us() - start_proc_time)/1e6
  print_summary(lowest, timer, proc_timer, membership, param, tour_history, cost_mat_read_time, instance_read_time, num_trials_feasible, num_trials, false)

  println("vd_info.update_ancestors_time ", vd_info.update_ancestors_time)
  println("vd_info.open_pop_time ", vd_info.open_pop_time)
  println("vd_info.closed_check_time ", vd_info.closed_check_time)
  println("vd_info.closed_push_time ", vd_info.closed_push_time)
  println("vd_info.ancestor_check_time ", vd_info.ancestor_check_time)
  println("vd_info.inf_and_prune_check_time ", vd_info.inf_and_prune_check_time)
  println("vd_info.succ_gen_time ", vd_info.succ_gen_time)
  println("vd_info.succ_closed_time ", vd_info.succ_closed_time)
  println("vd_info.seen_key_time ", vd_info.seen_key_time)
  println("vd_info.seen_update_time ", vd_info.seen_update_time)
  println("vd_info.open_push_time ", vd_info.open_push_time)
  println("vd_info.goal_check_time ", vd_info.goal_check_time)

  #=
  println("sum ", vd_info.update_ancestors_time + 
                  vd_info.open_pop_time + 
                  vd_info.closed_check_time + 
                  vd_info.closed_push_time + 
                  vd_info.ancestor_check_time + 
                  vd_info.inf_and_prune_check_time + 
                  vd_info.succ_gen_time + 
                  vd_info.succ_closed_time + 
                  vd_info.seen_key_time + 
                  vd_info.seen_update_time + 
                  vd_info.open_push_time + 
                  vd_info.goal_check_time)
  =#

  return powers
end

function parse_cmd(ARGS)
	if isempty(ARGS)
		println("no input instance given")
		exit(0)
	end
	if ARGS[1] == "-help" || ARGS[1] == "--help"
		println("Usage:  GTSPcmd.jl [filename] [optional flags]\n")
		println("Optional flags (vales are give in square brackets) :\n")
		println("-mode=[default, fast, slow]      (default is default)")
		println("-max_time=[Int]                  (default set by mode)")
		println("-trials=[Int]                    (default set by mode)")
		println("-restarts=[Int]                  (default set by mode)")
		println("-noise=[None, Both, Subset, Add] (default is Both)")
		println("-num_iterations=[Float]          (default set by mode. Number multiplied by # of sets)")
		println("-verbose=[0, 1, 2, 3]            (default is 3. 0 is no output, 3 is most.)")
		println("-output=[filename]               (default is None)")
		println("-epsilon=[Float in [0,1]]        (default is 0.5)")
		println("-reopt=[Float in [0,1]]          (default is 1.0)")
		println("-budget=[Int]                    (default has no budget)")
		println("-socket_port=[Int]               (default is 65432)")
		println("-lazy_edge_eval=[Int]            (default is 1)")
		println("-new_socket_each_instance=[filename]    (default is 0)")
		exit(0)
	end
	int_flags = ["-max_time", "-trials", "-restarts", "-verbose", "-budget", "-socket_port", "-lazy_edge_eval", "-new_socket_each_instance", "-max_removals_cap"]
	float_flags = ["-epsilon", "-reopt", "-num_iterations", "-latest_improvement", "-first_improvement", "-max_removal_fraction"]
	string_flags = ["-mode", "-output", "-noise", "-devel", "-init_tour"]
	filename = ""
	optional_args = Dict{Symbol, Any}()
	for arg in ARGS
		temp = split(arg, "=")
		if length(temp) == 1 && filename == ""
			filename = temp[1]
		elseif length(temp) == 2
			flag = temp[1]
			value = temp[2]
			if flag in int_flags
				key = Symbol(flag[2:end])
				optional_args[key] = parse(Int64, value)
			elseif flag in float_flags
				key = Symbol(flag[2:end])
				optional_args[key] = parse(Float64, value)
			elseif flag in string_flags
				key = Symbol(flag[2:end])
				optional_args[key] = value
			else
				println("WARNING: skipping unknown flag ", flag, " in command line arguments")
			end
		else
			error("argument ", arg, " not in proper format")
		end
	end
	return filename, optional_args
end

function main(args, max_time::Float64, inf_val::Int64, given_initial_tours::AbstractArray{Int64,1}, do_perf::Bool, perf_file::String, dist::AbstractArray{Int64,2}, call_gc::Bool)
  if occursin("custom0", args[1])
    println("Solving custom0.gtsp")
  end
  start_time_for_tour_history = time_ns()
  problem_instance, optional_args = parse_cmd(args)
  problem_instance = String(problem_instance)

	output_file = get(optional_args, :output, "None")
  if output_file != "None"
    f = open(output_file, "w")
    write(f, "\n")
    close(f)
  end

  optional_args[Symbol("max_time")] = max_time

  evaluated_edges = Vector{Tuple{Int64, Int64}}()
  open_tsp = false

  read_start_time = time_ns()
  num_vertices, num_sets, sets, _, membership = read_file(problem_instance, size(dist, 1) == 0)
  read_end_time = time_ns()
  instance_read_time = (read_end_time - read_start_time)/1.0e9
  # println("Reading GTSPLIB file took ", instance_read_time, " s")

  cost_mat_read_time = 0.

  if call_gc
    GC.gc()
  end
  timing_result = @timed GLNS.solver(problem_instance, TCPSocket(), given_initial_tours, start_time_for_tour_history, inf_val, evaluated_edges, open_tsp, num_vertices, num_sets, sets, dist, membership, instance_read_time, cost_mat_read_time, do_perf, perf_file; optional_args...)
  if get(optional_args, :verbose, 0) == 3
    println("Compile time: ", timing_result.compile_time)
  end
  return timing_result.value
end

function independent_multi_search(args::Vector{String}, max_time::Float64, inf_val::Int64, given_initial_tours::AbstractArray{Int64,1}, dist::AbstractArray{Int64,2}, call_gc::Bool)
  nthreads = Threads.nthreads()
  pinthreads(:cores)

  start_time_for_tour_history = time_ns()
  problem_instance, optional_args = parse_cmd(args)
  problem_instance = String(problem_instance)

	output_file = get(optional_args, :output, "None")
  if output_file != "None"
    f = open(output_file, "w")
    write(f, "\n")
    close(f)
  end

  optional_args[Symbol("max_time")] = max_time

  evaluated_edges = Vector{Tuple{Int64, Int64}}()
  open_tsp = false

  read_start_time = time_ns()
  num_vertices, num_sets, sets, _, membership = read_file(problem_instance, size(dist, 1) == 0)
  read_end_time = time_ns()
  instance_read_time = (read_end_time - read_start_time)/1.0e9
  # println("Reading GTSPLIB file took ", instance_read_time, " s")

  cost_mat_read_time = 0.

  if call_gc
    GC.gc()
  end

  # Need to make the copies here because thread 1 is going to start shuffling the sets once we enter the following for loop
  set_copies_per_thread = cat([sets], [deepcopy(sets) for thread_idx=2:nthreads], dims=1)

  # Don't seed within the solver function because that will make all threads generate the same solution
  Random.seed!(1234);

  @threads for thread_idx=1:nthreads
    this_optional_args = deepcopy(optional_args)
    this_optional_args[:output] = optional_args[:output][1:length(optional_args[:output]) - length(".tour")]*"_"*string(thread_idx)*".tour"
    GLNS.solver(problem_instance, TCPSocket(), given_initial_tours, start_time_for_tour_history, inf_val, evaluated_edges, open_tsp, num_vertices, num_sets, set_copies_per_thread[thread_idx], dist, membership, instance_read_time, cost_mat_read_time, false, "", Dict{String,Any}(), false; this_optional_args...)
  end
end

end
