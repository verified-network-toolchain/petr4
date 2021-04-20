""" Representation of Petr4 runtime objects. """
import base64
import collections

class Entry(object):

    def __init__(self, match, action, action_data):
        self.match = match
        self.action = action
        self.action_data = action_data

    def to_json(self):
        return { "match": self.match, "action" : self.action, "action_data" : self.action_data }
