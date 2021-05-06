""" Representation of Petr4 runtime objects. """
import base64
import collections

class Entry(object):

    def __init__(self, table, match, action, action_data):
        self.table = table
        self.match = []
        self.action = action
        self.action_data = []

    def __str__(self):
        return f"table={self.table}, action={self.action})"

    def to_json(self):
        return { "table" : self.table, 
                 "matches": self.match, 
                 "action" : self.action, 
                 "action_data" : self.action_data }
    
