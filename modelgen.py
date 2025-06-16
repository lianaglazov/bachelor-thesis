from itertools import product

class KripkeRailway:
    def __init__(self, stations, track_list, num_trains):
        self.stations = stations
        self.tracks = self.generate_tracks(track_list)
        self.num_trains = num_trains
        self.states = {}
        self.transitions = []
        self.generate_states()
        self.generate_transitions()

    def generate_tracks(self, track_list):
        tracks = []
        for way in track_list:
            i = 0
            for j in range(1, len(way)):
                tracks.append(way[i] + way[j])
                tracks.append(way[j] + way[i])
                i += 1
        return tracks

    def generate_states(self):
        base_locations = self.stations + self.tracks # a train can be either at a station or on a track
        # get the combinations of all trains
        # for i in range(1, self.num_trains + 1):
        train_ids = []
        n = self.num_trains
        for j in range(1, n+1):
            train_ids.append(f"t{j}")
        train_positions = product(base_locations, repeat = len(train_ids)) # cartesian product for the possible locations of the n trains
        for pos in train_positions:
            state = set((f"{train_ids[k]}{pos[k]}" for k in range(len(train_ids)))) # the state is a set of labels
            if self.validate(state): 
                state_name = f"s{len(self.states)}"
                self.states[state_name] = state

    def validate(self, state):
        station_counts = {s: 0 for s in self.stations}
        track_usage = []
        for label in state:
            location = label[2:] # as the labels are of type t1Location, we can get the location name out from it
            if location in self.stations:
                station_counts[location] += 1
                if station_counts[location] > 3:
                    return False  # if there are more than 3 trains in a station then the state is not valid
            elif location in self.tracks:
                if location in track_usage:
                    return False  # on a track can only be one train at a time
                stations = []
                for station in self.stations:
                    if station in location:
                        stations.append(station)
                track_usage.append(stations[0]+stations[1])
                track_usage.append(stations[1]+stations[0])
        return True

    def generate_transitions(self):
        for state in self.states.keys():
            for new_state in self.get_possible_moves(state):
                for k, s in self.states.items():
                    if s == new_state:
                        ns = k
                self.transitions.append((state, ns))

            # for new_state in self.add_train(state):
            #     for k, s in self.states.items():
            #         if s == new_state:
            #             ns = k
            #     self.transitions.append((state, ns))

    def get_possible_moves(self, state_key):
        possible_moves = []
        state = self.states[state_key]
        for label in state: # the transitions are based on each label of the state, that describe every train location, as we need constraints for all of them
            train, location = label[:2], label[2:]

            if location in self.stations: # if the train is in a station we check if we can go to a track adjacent to the station
                for track in self.tracks:# the tracks are labeled as concatenation of the two states it connects
                    if track[:len(location)] == location: # check if it is the right way track - when we leave a station we can only go on the tracks
                                                            # which name starts with the station
                        new_state = (state - {label}) | {f"{train}{track}"} 
                        if self.validate(new_state):
                            possible_moves.append(new_state)
            elif location in self.tracks: # if the train is on a track
                for station in self.stations: # get the stations adjacent to the track
                    if location[len(location) - len(station):] == station: # check if the station is at the end of the track
                        new_state = (state - {label}) | {f"{train}{station}"}
                        if self.validate(new_state):
                            possible_moves.append(new_state)
        return possible_moves

    # for the transitions to states with more trains
    # we can add a train to a station that is not full
    def add_train(self, state_key):
        state = self.states[state_key]
        existing_trains = {label[:2] for label in state}
        available_trains = {f"t{i+1}" for i in range(self.num_trains)} - existing_trains
        possible_additions = []

        for train in available_trains:
            for station in self.stations:
                if sum(1 for s in state if s[2:] == station) < 3:
                    new_state = state | {f"{train}{station}"}
                    if self.validate(new_state):
                        possible_additions.append(new_state)
        return possible_additions
    
    def print_model(self):
        print(f"{len(self.states)} states")
        for state in self.states:
            print(state, ":" ,self.states[state])
        
        print(f"\n{len(self.transitions)} transitions:")
        for (s1, s2) in self.transitions:
            print(f"{s1} -> {s2}")

    def generate_haskell_code(self):
        transitions = []
        
        transition_dict = {state_name: [] for state_name in self.states}
        
        for (from_state, to_state) in self.transitions:
            transition_dict[from_state].append(to_state)
        
        for state_name, next_states in transition_dict.items():
            next_states_str = ', '.join([f'"{next_state}"' for next_state in next_states])
            transitions.append(f'    "{state_name}" -> [{next_states_str}]')

        labels = []
        for state_name, state in self.states.items():
            labels_for_state = [f'"{label}"' for label in state]
            labels.append(f'    "{state_name}" -> [{", ".join(labels_for_state)}]')

        states_str = ', '.join([f'"{state_name}"' for state_name in self.states])
        
        initial_states = ', '.join(f'"{state_name}"' for state_name, state in self.states.items()
                                if all(label[2:] in self.stations for label in state))

        hs_code = f"""
{{-# LANGUAGE LambdaCase #-}}

module Study.Case where

import Models (Model(..))

model = Model {{
    states = [{states_str}],
    initialStates = [{initial_states}],
    transition = \\case
{''.join([f'\n{t}' for t in transitions])}
    ,
    labels = \\case
{''.join([f'\n{l}' for l in labels])}
}}
"""
        return hs_code
        
    def generate_haskell_code2(self):
        transition_dict = {state_name: [] for state_name in self.states}
        
        for (from_state, to_state) in self.transitions:
            transition_dict[from_state].append(to_state)

        transitions_str = ',\n    '.join(f'("{from_state}", Set.fromList [{", ".join(f'" {to_state}"' for to_state in to_states)}])' for from_state, to_states in transition_dict.items())
        labels_str = ',\n    '.join(f'("{state_name}", Set.fromList [{", ".join(f'" {label}"' for label in labels)}])' for state_name, labels in self.states.items())
        
        states_str = ', '.join([f'"{state_name}"' for state_name in self.states])
        initial_states = ', '.join(f'"{state_name}"' for state_name, state in self.states.items()
                                if any(label[2:] in self.stations for label in state))

        hs_code = f"""
{{-# LANGUAGE LambdaCase #-}}

module Study.Case2 where

import Models (Model2(..))

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map

model2 = Model2 {{
    states2 = Set.fromList [{states_str}],
    initialStates2 = Set.fromList [{initial_states}],
    transition2 = Map.fromList [{transitions_str}] 
    ,
    labels2 = Map.fromList[{labels_str}]
}}
"""
        return hs_code
    
    def export_to_file(self, filename="study\\Case.hs"):
        hs_code = self.generate_haskell_code()
        with open(filename, "w") as f:
            f.write(hs_code)
    def export_to_file2(self, filename="study\\Case2.hs"):
        hs_code = self.generate_haskell_code2()
        with open(filename, "w") as f:
            f.write(hs_code)



stations = ["A", "B", "C"]
# tracks = ["AB", "BC"]
# dam tracks ca o lista de liste de cai posibile
tracks = [["A", "B", "C"]] # putem sa circulam pe A -> B -> C si inapoi adica avem tracks intre AB si BC
# daca aveam 4 statii si [["A", "B", "C", "D"] ["B", "D"]] aveam odata legatura A->B->C->D si apoi B->D, adica trackurile AB, BC, CD si BD
# etichetele pt trackuri se vor calcula in clasa modelui pe baza acestei liste

# stations = ["A", "B", "C", "D"]
# tracks = [["A","B","C"], ["B", "D"]]
num_trains = 2

kripke = KripkeRailway(stations, tracks, num_trains)
kripke.print_model()
kripke.export_to_file()
kripke.export_to_file2()

