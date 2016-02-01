sig UserProfile { 
  portrait: disj one Photo
}
sig Album {
  photos: disj some Photo
} /*{
  #photos > 0
}*/

sig Photo { 
  photoable_type: one PR_PhotoableTypeField
  // photable_id は定義しない。
}

abstract sig PR_PhotoableTypeField {
  --photos_identify: one Photo
}
sig UserProfile_Photoable extends PR_PhotoableTypeField { 
  user_profile: disj one UserProfile
}
sig Album_Photoable extends PR_PhotoableTypeField { 
  album: some Album
}

fact {
  --photoable_type = ~photos_identify
  all photo:Photo | photo = (Photo<:photoable_type).(photo.(Photo<:photoable_type))
  Photo.photoable_type = PR_PhotoableTypeField
  portrait = ~(photoable_type.user_profile)
  photos = ~(photoable_type.album)
}

run {} // for 4 but 8 Photo
