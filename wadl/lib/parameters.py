class Parameters(dict):
    """docstring for Parameters"""

    def __init__(self, default=True):
        if default:
            self.setDefaults()

    def setDefaults(self):
        raise NotImplementedError()
