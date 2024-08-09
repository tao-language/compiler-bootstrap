class record:
    def __init__(self, **kwargs):
        self.__dict__ = kwargs

    def __eq__(self, other):
        return self.__dict__ == other.__dict__

    def __ne__(self, other):
        return self.__dict__ != other.__dict__
