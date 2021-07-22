# -*- coding: utf-8 -*-
from __future__ import print_function, division
import pygame

class Canvas():
    def __init__(self,width,height):
        pygame.init()
        pygame.key.set_repeat(3,0)
        self.screen = pygame.display.set_mode((width,height)) 
        self.background = pygame.Surface((self.screen.get_size()))
        self.background.fill((0,0,0)) # fill black
        self.background = self.background.convert()

    def clear(self):
        self.background.fill((0,0,0)) 
        
    def redraw(self):
        self.screen.blit(self.background,(0,0))        
        pygame.display.flip() # flip the screen 30 times a second

    def paint_point(self,p,color):
        height = self.screen.get_rect().height
        width = self.screen.get_rect().width
        x = int(p.x) % width
        y = - int(p.y) % height
        pygame.draw.circle(self.background,color,(x,y),1)
