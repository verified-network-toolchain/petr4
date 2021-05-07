""" Representation of Petr4 runtime objects. """
import base64
import collections

class Entry(object):

    def __init__(self, table, matches, action, action_data):
        self.table = table
        self.matches = matches
        self.action = action
        self.action_data = action_data

    def __str__(self):
        matches_str = ",".join([f"{x}={v}" for x,v in self.matches ])
        action_data_str = ",".join([f"{x}={v}" for x,v in self.action_data ])
        return f"table={self.table}, matches=[{matches_str}], action={self.action}, action_data=[{action_data_str}])"

    def to_json(self):
        return { "table" : self.table, 
                 "matches": self.matches, 
                 "action" : self.action, 
                 "action_data" : self.action_data }
    
